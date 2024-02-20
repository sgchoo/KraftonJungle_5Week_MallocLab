/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Choo SungKyul",
    /* First member's email address */
    "choosg@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};



/* ------------------------------------------------------------------------------------------------------------------------------------- */
/*-------------------------------------------------------------DEFINE--------------------------------------------------------------------*/
/* ------------------------------------------------------------------------------------------------------------------------------------- */



#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 8의 배수로 padding

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE               4
#define DSIZE               8
#define CHUNKSIZE           (1 << 12)

#define MAX(x, y)           ((x) > (y)) ? (x) : (y)

#define PACK(size, alloc)   ((size) | (alloc))

#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, size)        (*(unsigned int *)(p) = size)

#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_FREE_BLOCK(bp) (*(void **)((bp) + WSIZE))
#define PREV_FREE_BLOCK(bp) (*(void **)(bp))



/* ------------------------------------------------------------------------------------------------------------------------------------------- */
/* ------------------------------------------------- Global variable & Function -------------------------------------------------------------- */
/* ------------------------------------------------------------------------------------------------------------------------------------------- */



/* Global variable & Function */
static char *free_listp;

static void *extend_heap(size_t words);
static void RemoveBlock(void *bp);
static void AddBlock(void *bp);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);



/* ------------------------------------------------------------------------------------------------------------------------------------------ */
/* ------------------------------------------------------Function Code----------------------------------------------------------------------- */
/* ------------------------------------------------------------------------------------------------------------------------------------------ */



/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((free_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;

    PUT(free_listp, 0);
    PUT(free_listp + (1 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(free_listp + (2 * WSIZE), NULL);
    PUT(free_listp + (3 * WSIZE), NULL);
    PUT(free_listp + (4 * WSIZE), PACK(2 * DSIZE, 1));          
    PUT(free_listp + (5 * WSIZE), PACK(0, 1));              
    free_listp += 2 * WSIZE;                                

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void RemoveBlock(void *bp)
{
    if(bp == free_listp)
    {
        free_listp = NEXT_FREE_BLOCK(bp);
        if(free_listp != NULL)
            PREV_FREE_BLOCK(free_listp) = NULL;
        return;
    }

    NEXT_FREE_BLOCK(PREV_FREE_BLOCK(bp)) = NEXT_FREE_BLOCK(bp);
    if(NEXT_FREE_BLOCK(bp) != NULL)
        PREV_FREE_BLOCK(NEXT_FREE_BLOCK(bp)) = PREV_FREE_BLOCK(bp);
}

static void AddBlock(void *bp)
{
    NEXT_FREE_BLOCK(bp) = free_listp;
    PREV_FREE_BLOCK(bp) = NULL;
    if(free_listp != NULL)
        PREV_FREE_BLOCK(free_listp) = bp;
    free_listp = bp;
}

static void *coalesce(void *bp)
{
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc)
    {
        AddBlock(bp);
        return bp;
    }

    else if(prev_alloc && !next_alloc)
    {
        RemoveBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        AddBlock(bp);
    }

    else if(!prev_alloc && next_alloc)
    {
        RemoveBlock(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        AddBlock(bp);
    }

    else
    {
        RemoveBlock(PREV_BLKP(bp));
        RemoveBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        AddBlock(bp);
    }

    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/*
두 번째 힙 영역이 할당될 때, 기존에 있던 영역과 연결해주기 위해.
*/

static void *first_fit(size_t asize)
{
    char *tempBp = free_listp;

    while(tempBp != NULL)
    {
        if(GET_SIZE(HDRP(tempBp)) >= asize)
            return tempBp;
        tempBp = NEXT_FREE_BLOCK(tempBp);
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t beforeFreeBlkSize = GET_SIZE(HDRP(bp));

    RemoveBlock(bp);

    if((beforeFreeBlkSize - asize) >= (2*DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(beforeFreeBlkSize - asize, 0));
        PUT(FTRP(bp), PACK(beforeFreeBlkSize - asize, 0));
        AddBlock(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(beforeFreeBlkSize, 1));
        PUT(FTRP(bp), PACK(beforeFreeBlkSize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendSize;
    char *bp;

    if(size == 0)
        return NULL;

    // header, footer가 달리니, 8byte 배수 크기로 맞춰준다.
    if(size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    if((bp = first_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 할당된 힙 영역에 공간이 없을때
    extendSize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendSize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
