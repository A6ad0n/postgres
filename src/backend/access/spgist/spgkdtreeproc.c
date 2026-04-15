/*-------------------------------------------------------------------------
 *
 * spgkdtreeproc.c
 *	  implementation of k-d tree over points for SP-GiST
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *			src/backend/access/spgist/spgkdtreeproc.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/spgist.h"
#include "access/spgist_private.h"
#include "access/stratnum.h"
#include "catalog/pg_type.h"
#include "utils/float.h"
#include "utils/fmgrprotos.h"
#include "utils/geo_decls.h"

#include "portability/instr_time.h"
#include "utils/timestamp.h"
#include "math.h"
#include <float.h>


Datum
spg_kd_config(PG_FUNCTION_ARGS)
{
#ifdef NOT_USED
	spgConfigIn *cfgin = (spgConfigIn *) PG_GETARG_POINTER(0);
#endif
	spgConfigOut *cfg = (spgConfigOut *) PG_GETARG_POINTER(1);

	cfg->prefixType = FLOAT8OID;
	cfg->labelType = VOIDOID;	/* we don't need node labels */
	cfg->canReturnData = true;
	cfg->longValuesOK = false;
	PG_RETURN_VOID();
}

static int
getSide(double coord, bool isX, Point *tst)
{
	double		tstcoord = (isX) ? tst->x : tst->y;

	if (coord == tstcoord)
		return 0;
	else if (coord > tstcoord)
		return 1;
	else
		return -1;
}

Datum
spg_kd_choose(PG_FUNCTION_ARGS)
{
	spgChooseIn *in = (spgChooseIn *) PG_GETARG_POINTER(0);
	spgChooseOut *out = (spgChooseOut *) PG_GETARG_POINTER(1);
	Point	   *inPoint = DatumGetPointP(in->datum);
	double		coord;

	if (in->allTheSame)
		elog(ERROR, "allTheSame should not occur for k-d trees");

	Assert(in->hasPrefix);
	coord = DatumGetFloat8(in->prefixDatum);

	Assert(in->nNodes == 2);

	out->resultType = spgMatchNode;
	out->result.matchNode.nodeN =
		(getSide(coord, in->level % 2, inPoint) > 0) ? 0 : 1;
	out->result.matchNode.levelAdd = 1;
	out->result.matchNode.restDatum = PointPGetDatum(inPoint);

	PG_RETURN_VOID();
}

typedef struct SortedPoint
{
	Point	   *p;
	int			i;
} SortedPoint;

static int
x_cmp(const void *a, const void *b)
{
	const SortedPoint *pa = a;
	const SortedPoint *pb = b;

	if (pa->p->x == pb->p->x)
		return 0;
	return (pa->p->x > pb->p->x) ? 1 : -1;
}

static int
y_cmp(const void *a, const void *b)
{
	const SortedPoint *pa = a;
	const SortedPoint *pb = b;

	if (pa->p->y == pb->p->y)
		return 0;
	return (pa->p->y > pb->p->y) ? 1 : -1;
}

static int
partition(SortedPoint *arr, int left, int right, int pivotIndex, int axis)
{
    double pivotValue = axis ? arr[pivotIndex].p->x : arr[pivotIndex].p->y;

    SortedPoint tmp = arr[pivotIndex];
    arr[pivotIndex] = arr[right];
    arr[right] = tmp;

    int storeIndex = left;

    for (int i = left; i < right; i++)
    {
        double v = axis ? arr[i].p->x : arr[i].p->y;

        if (v < pivotValue)
        {
            SortedPoint t = arr[storeIndex];
            arr[storeIndex] = arr[i];
            arr[i] = t;
            storeIndex++;
        }
    }

    SortedPoint t = arr[right];
    arr[right] = arr[storeIndex];
    arr[storeIndex] = t;

    return storeIndex;
}

static void
quickselect(SortedPoint *arr, int left, int right, int k, int axis)
{
    while (left < right)
    {
        int pivotIndex = (left + right) / 2;
        pivotIndex = partition(arr, left, right, pivotIndex, axis);

        if (k == pivotIndex)
            return;
        else if (k < pivotIndex)
            right = pivotIndex - 1;
        else
            left = pivotIndex + 1;
    }
}

static void
spg_kd_picksplit_opt(spgPickSplitIn *in, spgPickSplitOut *out)
{
    instr_time start, end;
    INSTR_TIME_SET_CURRENT(start);

    int i, middle = in->nTuples >> 1;
    SortedPoint *arr;
    double coord;

    int axis_flag = (in->level % 2);
    const char *axis = axis_flag ? "X" : "Y";

    double min = DBL_MAX, max = -DBL_MAX, sum = 0;
    int duplicates = 0;

    arr = palloc_array(SortedPoint, in->nTuples);

    for (i = 0; i < in->nTuples; i++)
    {
        arr[i].p = DatumGetPointP(in->datums[i]);
        arr[i].i = i;
    }

    quickselect(arr, 0, in->nTuples - 1, middle, axis_flag);

    coord = axis_flag ? arr[middle].p->x : arr[middle].p->y;

    for (i = 0; i < in->nTuples; i++)
    {
        double v = axis_flag ? arr[i].p->x : arr[i].p->y;

        if (v < min) min = v;
        if (v > max) max = v;
        sum += v;

        if (i > 0)
        {
            double prev = axis_flag
                ? arr[i-1].p->x
                : arr[i-1].p->y;

            if (prev == v)
                duplicates++;
        }
    }

    double avg = sum / in->nTuples;

    out->hasPrefix = true;
    out->prefixDatum = Float8GetDatum(coord);

    out->nNodes = 2;
    out->nodeLabels = NULL;

    out->mapTuplesToNodes = palloc_array(int, in->nTuples);
    out->leafTupleDatums = palloc_array(Datum, in->nTuples);

    for (i = 0; i < in->nTuples; i++)
    {
        Point *p = arr[i].p;
        int n = arr[i].i;

        out->mapTuplesToNodes[n] = (i < middle) ? 0 : 1;
        out->leafTupleDatums[n] = PointPGetDatum(p);
    }

    INSTR_TIME_SET_CURRENT(end);
    INSTR_TIME_SUBTRACT(end, start);

    double elapsed = INSTR_TIME_GET_DOUBLE(end) * 1000;

    elog(LOG,
         "[KD][OPT] done n=%d level=%d axis=%s left=%d right=%d "
         "balance=%.3f min=%.6f max=%.6f span=%.6f avg=%.6f dup=%d coord=%.6f time=%.3fms",
         in->nTuples,
         in->level,
         axis,
         middle,
         in->nTuples - middle,
         (double)middle / in->nTuples,
         min,
         max,
         max - min,
         avg,
         duplicates,
         coord,
         elapsed);
}

static void
spg_kd_picksplit_base(spgPickSplitIn *in, spgPickSplitOut *out)
{
    instr_time start, end;
    INSTR_TIME_SET_CURRENT(start);

    int i, middle;
    SortedPoint *sorted;
    double coord;

    double min = DBL_MAX, max = -DBL_MAX, sum = 0;
    int duplicates = 0;

    const char *axis = (in->level % 2) ? "X" : "Y";

    sorted = palloc_array(SortedPoint, in->nTuples);

    for (i = 0; i < in->nTuples; i++)
    {
        sorted[i].p = DatumGetPointP(in->datums[i]);
        sorted[i].i = i;
    }

    qsort(sorted, in->nTuples, sizeof(*sorted),
          (in->level % 2) ? x_cmp : y_cmp);

    middle = in->nTuples >> 1;

    coord = (in->level % 2) ? sorted[middle].p->x : sorted[middle].p->y;

    /* stats */
    for (i = 0; i < in->nTuples; i++)
    {
        double v = (in->level % 2) ? sorted[i].p->x : sorted[i].p->y;

        if (v < min) min = v;
        if (v > max) max = v;
        sum += v;

        if (i > 0)
        {
            double prev = (in->level % 2)
                ? sorted[i-1].p->x
                : sorted[i-1].p->y;

            if (prev == v)
                duplicates++;
        }
    }

    double avg = sum / in->nTuples;

    out->hasPrefix = true;
    out->prefixDatum = Float8GetDatum(coord);

    out->nNodes = 2;
    out->nodeLabels = NULL;

    out->mapTuplesToNodes = palloc_array(int, in->nTuples);
    out->leafTupleDatums = palloc_array(Datum, in->nTuples);

    for (i = 0; i < in->nTuples; i++)
    {
        Point *p = sorted[i].p;
        int n = sorted[i].i;

        out->mapTuplesToNodes[n] = (i < middle) ? 0 : 1;
        out->leafTupleDatums[n] = PointPGetDatum(p);
    }

    INSTR_TIME_SET_CURRENT(end);
    INSTR_TIME_SUBTRACT(end, start);

    double elapsed = INSTR_TIME_GET_DOUBLE(end) * 1000;

    elog(LOG,
         "[KD][BASE] done n=%d level=%d axis=%s left=%d right=%d "
         "balance=%.3f min=%.6f max=%.6f span=%.6f avg=%.6f dup=%d coord=%.6f time=%.3fms",
         in->nTuples,
         in->level,
         axis,
         middle,
         in->nTuples - middle,
         (double)middle / in->nTuples,
         min,
         max,
         max - min,
         avg,
         duplicates,
         coord,
         elapsed);
}

#define DUP_THRESHOLD 0.2
#define VAR_THRESHOLD_LOW 0.01
#define VAR_THRESHOLD_HIGH 1.0

static void
spg_kd_picksplit_adaptive(spgPickSplitIn *in, spgPickSplitOut *out)
{
    instr_time start, end;
    INSTR_TIME_SET_CURRENT(start);

    int i;
    int axis_flag = (in->level % 2);
    const char *axis = axis_flag ? "X" : "Y";

    SortedPoint *arr = palloc_array(SortedPoint, in->nTuples);

    double min = DBL_MAX, max = -DBL_MAX;
    double sum = 0, sum_sq = 0;
    int left = 0;

    for (i = 0; i < in->nTuples; i++)
    {
        arr[i].p = DatumGetPointP(in->datums[i]);
        arr[i].i = i;

        double v = axis_flag ? arr[i].p->x : arr[i].p->y;

        if (v < min) min = v;
        if (v > max) max = v;

        sum += v;
        sum_sq += v * v;
    }

    double mean = sum / in->nTuples;
    double variance = sum_sq / in->nTuples - mean * mean;
    double span = max - min;

    const char *strategy = "MEDIAN";
    double coord = mean;
    int split_index = in->nTuples >> 1;

    qsort(arr, in->nTuples, sizeof(*arr),
        axis_flag ? x_cmp : y_cmp);

    int duplicates = 0;
    for (i = 1; i < in->nTuples; i++)
    {
        double prev = axis_flag ? arr[i-1].p->x : arr[i-1].p->y;
        double curr = axis_flag ? arr[i].p->x : arr[i].p->y;

        if (prev == curr)
            duplicates++;
    }

    /* --- handle degenerate case early --- */
    if (span == 0.0)
    {
        strategy = "FORCED";

        out->hasPrefix = true;
        coord = axis_flag ? arr[split_index].p->x : arr[split_index].p->y;
        out->prefixDatum = Float8GetDatum(coord);

        out->nNodes = 2;
        out->nodeLabels = NULL;

        out->mapTuplesToNodes = palloc_array(int, in->nTuples);
        out->leafTupleDatums = palloc_array(Datum, in->nTuples);

        for (i = 0; i < in->nTuples; i++)
        {
            int n = arr[i].i;
            out->mapTuplesToNodes[n] = (i < split_index) ? 0 : 1;
            out->leafTupleDatums[n] = PointPGetDatum(arr[i].p);
        }

        int left = split_index;
        int right = in->nTuples - split_index;
    } else 
    {
        double dup_ratio = (double)duplicates / in->nTuples;

        if (dup_ratio > 0.2)
        {
            strategy = "MEDIAN";
        }
        else if (variance < 0.01)
        {
            strategy = "MEAN";
            coord = mean;
        }
        else if (variance > 1.0)
        {
            strategy = "VAR";
        }
        else
        {
            strategy = "MEDIAN";
        }


        if (strcmp(strategy, "MEDIAN") == 0)
        {
            split_index = in->nTuples >> 1;
            coord = axis_flag ? arr[split_index].p->x : arr[split_index].p->y;
        }
        else if (strcmp(strategy, "VAR") == 0)
        {
            double *prefix = palloc(sizeof(double) * in->nTuples);
            double *prefix_sq = palloc(sizeof(double) * in->nTuples);

            for (i = 0; i < in->nTuples; i++)
            {
                double v = axis_flag ? arr[i].p->x : arr[i].p->y;

                prefix[i] = v + (i ? prefix[i-1] : 0);
                prefix_sq[i] = v*v + (i ? prefix_sq[i-1] : 0);
            }

            double best_score = DBL_MAX;

            for (i = 1; i < in->nTuples - 1; i++)
            {
                int ln = i;
                int rn = in->nTuples - i;

                double lsum = prefix[i-1];
                double lsq = prefix_sq[i-1];

                double rsum = prefix[in->nTuples-1] - lsum;
                double rsq = prefix_sq[in->nTuples-1] - lsq;

                double lvar = lsq/ln - (lsum/ln)*(lsum/ln);
                double rvar = rsq/rn - (rsum/rn)*(rsum/rn);

                double score = lvar * ln + rvar * rn;

                if (score < best_score)
                {
                    best_score = score;
                    split_index = i;
                }
            }

            coord = axis_flag
                ? arr[split_index].p->x
                : arr[split_index].p->y;
        }


        out->hasPrefix = true;
        out->prefixDatum = Float8GetDatum(coord);

        out->nNodes = 2;
        out->nodeLabels = NULL;

        out->mapTuplesToNodes = palloc_array(int, in->nTuples);
        out->leafTupleDatums = palloc_array(Datum, in->nTuples);

        for (i = 0; i < in->nTuples; i++)
        {
            Point *p = arr[i].p;
            int n = arr[i].i;

            int side = ((axis_flag ? p->x : p->y) < coord) ? 0 : 1;

            if (side == 0) left++;

            out->mapTuplesToNodes[n] = side;
            out->leafTupleDatums[n] = PointPGetDatum(p);
        }

        /* --- prevent empty split --- */
        if (left == 0 || left == in->nTuples)
        {
            int half = in->nTuples >> 1;

            for (i = 0; i < in->nTuples; i++)
            {
                int n = arr[i].i;
                out->mapTuplesToNodes[n] = (i < half) ? 0 : 1;
            }

            left = half;

            elog(LOG, "[KD][ADAPT] fallback forced split triggered");
        }
    }
    INSTR_TIME_SET_CURRENT(end);
    INSTR_TIME_SUBTRACT(end, start);

    double elapsed = INSTR_TIME_GET_DOUBLE(end) * 1000;

    int right = in->nTuples - left;

    elog(LOG,
        "[KD][ADAPT] done n=%d level=%d axis=%s left=%d right=%d "
        "balance=%.3f min=%.6f max=%.6f span=%.6f avg=%.6f dup=%d coord=%.6f time=%.3fms strategy=%s",
        in->nTuples,
        in->level,
        axis,
        left,
        right,
        (double)left / in->nTuples,
        min,
        max,
        span,
        mean,
        duplicates,
        coord,
        elapsed,
        strategy);
}

static void
spg_kd_picksplit_mean(spgPickSplitIn *in, spgPickSplitOut *out)
{
    instr_time start, end;
    INSTR_TIME_SET_CURRENT(start);

    int i, middle;
    SortedPoint *sorted;
    double coord;

    double min = DBL_MAX, max = -DBL_MAX, sum = 0;
    int duplicates = 0;

    const char *axis = (in->level % 2) ? "X" : "Y";

    sorted = palloc_array(SortedPoint, in->nTuples);

    for (i = 0; i < in->nTuples; i++)
    {
        sorted[i].p = DatumGetPointP(in->datums[i]);
        sorted[i].i = i;
    }

    qsort(sorted, in->nTuples, sizeof(*sorted),
          (in->level % 2) ? x_cmp : y_cmp);

    sum = 0;

    for (i = 0; i < in->nTuples; i++)
    {
        double v = (in->level % 2) ? sorted[i].p->x : sorted[i].p->y;
        sum += v;
    }

    coord = sum / in->nTuples;
    sum = 0;

    /* stats */
    for (i = 0; i < in->nTuples; i++)
    {
        double v = (in->level % 2) ? sorted[i].p->x : sorted[i].p->y;

        if (v < min) min = v;
        if (v > max) max = v;
        sum += v;

        if (i > 0)
        {
            double prev = (in->level % 2)
                ? sorted[i-1].p->x
                : sorted[i-1].p->y;

            if (prev == v)
                duplicates++;
        }
    }

    double avg = sum / in->nTuples;

    out->hasPrefix = true;
    out->prefixDatum = Float8GetDatum(coord);

    out->nNodes = 2;
    out->nodeLabels = NULL;

    out->mapTuplesToNodes = palloc_array(int, in->nTuples);
    out->leafTupleDatums = palloc_array(Datum, in->nTuples);

    int left = 0;

    for (i = 0; i < in->nTuples; i++)
    {
        Point *p = sorted[i].p;
        int n = sorted[i].i;

        int side = ((in->level % 2 ? p->x : p->y) < coord) ? 0 : 1;

        if (side == 0)
            left++;

        out->mapTuplesToNodes[n] = side;
        out->leafTupleDatums[n] = PointPGetDatum(p);
    }

    /* --- prevent empty split --- */
    if (left == 0 || left == in->nTuples)
    {
        int half = in->nTuples >> 1;

        for (i = 0; i < in->nTuples; i++)
        {
            int n = sorted[i].i;
            out->mapTuplesToNodes[n] = (i < half) ? 0 : 1;
        }

        left = half;
    }

    INSTR_TIME_SET_CURRENT(end);
    INSTR_TIME_SUBTRACT(end, start);

    double elapsed = INSTR_TIME_GET_DOUBLE(end) * 1000;

    elog(LOG,
         "[KD][MEAN] done n=%d level=%d axis=%s left=%d right=%d "
         "balance=%.3f min=%.6f max=%.6f span=%.6f avg=%.6f dup=%d coord=%.6f time=%.3fms",
         in->nTuples,
         in->level,
         axis,
         left,
         in->nTuples - left,
         (double)left / in->nTuples,
         min,
         max,
         max - min,
         avg,
         duplicates,
         coord,
         elapsed);
}

Datum
spg_kd_inner_consistent(PG_FUNCTION_ARGS)
{
	spgInnerConsistentIn *in = (spgInnerConsistentIn *) PG_GETARG_POINTER(0);
	spgInnerConsistentOut *out = (spgInnerConsistentOut *) PG_GETARG_POINTER(1);
	double		coord;
	int			which;
	int			i;
	BOX			bboxes[2];

	Assert(in->hasPrefix);
	coord = DatumGetFloat8(in->prefixDatum);

	if (in->allTheSame)
		elog(ERROR, "allTheSame should not occur for k-d trees");

	Assert(in->nNodes == 2);

	/* "which" is a bitmask of children that satisfy all constraints */
	which = (1 << 1) | (1 << 2);

	for (i = 0; i < in->nkeys; i++)
	{
		Point	   *query = DatumGetPointP(in->scankeys[i].sk_argument);
		BOX		   *boxQuery;

		switch (in->scankeys[i].sk_strategy)
		{
			case RTLeftStrategyNumber:
				if ((in->level % 2) != 0 && FPlt(query->x, coord))
					which &= (1 << 1);
				break;
			case RTRightStrategyNumber:
				if ((in->level % 2) != 0 && FPgt(query->x, coord))
					which &= (1 << 2);
				break;
			case RTSameStrategyNumber:
				if ((in->level % 2) != 0)
				{
					if (FPlt(query->x, coord))
						which &= (1 << 1);
					else if (FPgt(query->x, coord))
						which &= (1 << 2);
				}
				else
				{
					if (FPlt(query->y, coord))
						which &= (1 << 1);
					else if (FPgt(query->y, coord))
						which &= (1 << 2);
				}
				break;
			case RTBelowStrategyNumber:
			case RTOldBelowStrategyNumber:
				if ((in->level % 2) == 0 && FPlt(query->y, coord))
					which &= (1 << 1);
				break;
			case RTAboveStrategyNumber:
			case RTOldAboveStrategyNumber:
				if ((in->level % 2) == 0 && FPgt(query->y, coord))
					which &= (1 << 2);
				break;
			case RTContainedByStrategyNumber:

				/*
				 * For this operator, the query is a box not a point.  We
				 * cheat to the extent of assuming that DatumGetPointP won't
				 * do anything that would be bad for a pointer-to-box.
				 */
				boxQuery = DatumGetBoxP(in->scankeys[i].sk_argument);

				if ((in->level % 2) != 0)
				{
					if (FPlt(boxQuery->high.x, coord))
						which &= (1 << 1);
					else if (FPgt(boxQuery->low.x, coord))
						which &= (1 << 2);
				}
				else
				{
					if (FPlt(boxQuery->high.y, coord))
						which &= (1 << 1);
					else if (FPgt(boxQuery->low.y, coord))
						which &= (1 << 2);
				}
				break;
			default:
				elog(ERROR, "unrecognized strategy number: %d",
					 in->scankeys[i].sk_strategy);
				break;
		}

		if (which == 0)
			break;				/* no need to consider remaining conditions */
	}

	/* We must descend into the children identified by which */
	out->nNodes = 0;

	/* Fast-path for no matching children */
	if (!which)
		PG_RETURN_VOID();

	out->nodeNumbers = palloc_array(int, 2);

	/*
	 * When ordering scan keys are specified, we've to calculate distance for
	 * them.  In order to do that, we need calculate bounding boxes for both
	 * children nodes.  Calculation of those bounding boxes on non-zero level
	 * require knowledge of bounding box of upper node.  So, we save bounding
	 * boxes to traversalValues.
	 */
	if (in->norderbys > 0)
	{
		BOX			infArea;
		BOX		   *area;

		out->distances = palloc_array(double *, in->nNodes);
		out->traversalValues = palloc_array(void *, in->nNodes);

		if (in->level == 0)
		{
			float8		inf = get_float8_infinity();

			infArea.high.x = inf;
			infArea.high.y = inf;
			infArea.low.x = -inf;
			infArea.low.y = -inf;
			area = &infArea;
		}
		else
		{
			area = (BOX *) in->traversalValue;
			Assert(area);
		}

		bboxes[0].low = area->low;
		bboxes[1].high = area->high;

		if (in->level % 2)
		{
			/* split box by x */
			bboxes[0].high.x = bboxes[1].low.x = coord;
			bboxes[0].high.y = area->high.y;
			bboxes[1].low.y = area->low.y;
		}
		else
		{
			/* split box by y */
			bboxes[0].high.y = bboxes[1].low.y = coord;
			bboxes[0].high.x = area->high.x;
			bboxes[1].low.x = area->low.x;
		}
	}

	for (i = 1; i <= 2; i++)
	{
		if (which & (1 << i))
		{
			out->nodeNumbers[out->nNodes] = i - 1;

			if (in->norderbys > 0)
			{
				MemoryContext oldCtx = MemoryContextSwitchTo(in->traversalMemoryContext);
				BOX		   *box = box_copy(&bboxes[i - 1]);

				MemoryContextSwitchTo(oldCtx);

				out->traversalValues[out->nNodes] = box;

				out->distances[out->nNodes] = spg_key_orderbys_distances(BoxPGetDatum(box), false,
																		 in->orderbys, in->norderbys);
			}

			out->nNodes++;
		}
	}

	/* Set up level increments, too */
	out->levelAdds = palloc_array(int, 2);
	out->levelAdds[0] = 1;
	out->levelAdds[1] = 1;

	PG_RETURN_VOID();
}

/*
 * spg_kd_leaf_consistent() is the same as spg_quad_leaf_consistent(),
 * since we support the same operators and the same leaf data type.
 * So we just borrow that function.
 */

Datum
spg_kd_picksplit(PG_FUNCTION_ARGS)
{
	spgPickSplitIn *in = (spgPickSplitIn *) PG_GETARG_POINTER(0);
	spgPickSplitOut *out = (spgPickSplitOut *) PG_GETARG_POINTER(1);

	spg_kd_picksplit_base(in, out);
	// spg_kd_picksplit_opt(in, out);
    // spg_kd_picksplit_adaptive(in, out);
    // spg_kd_picksplit_mean(in, out);

    // НЕ ВЫШЛО
    // spg_kd_picksplit_var(in, out);

	PG_RETURN_VOID();
}