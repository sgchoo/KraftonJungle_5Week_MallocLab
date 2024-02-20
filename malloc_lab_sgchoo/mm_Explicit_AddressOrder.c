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



/* single word (4) or double word (8) alignment */
#define ALIGNMENT                 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size)               (((size) + (ALIGNMENT - 1)) & ~0x7) // 8의 배수로 padding

#define SIZE_T_SIZE               (ALIGN(sizeof(size_t)))

#define WSIZE                     4
#define DSIZE                     8
#define CHUNKSIZE                 (1 << 12)                   // 4096byte

#define MAX(x, y)                 ((x) > (y)) ? (x) : (y)

#define PACK(size, alloc)         ((size) | (alloc))          // or연산자로 사이즈 + 할당 여부 반환

#define GET(p)                    (*(unsigned int *)(p))          // get
#define PUT(p, size)              (*(unsigned int *)(p) = size)   // set

#define GET_SIZE(p)               (GET(p) & ~0x7)             // 뒷자리 3개를 제외한 나머지 수 즉, 해당 블록의 사이즈 반환
#define GET_ALLOC(p)              (GET(p) & 0x1)              // 뒷자리 3개만 확인 즉, 해당 블록의 할당 여부 반환

#define HDRP(bp)                  ((char *)(bp) - WSIZE)                      // header block
#define FTRP(bp)                  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer block

#define NEXT_BLKP(bp)             ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)             ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_FREEBLOCK(bp)        (*(void **)((bp) + WSIZE))
#define PREV_FREEBLOCK(bp)        (*(void **)(bp))



/* ------------------------------------------------------------------------------------------------------------------------------------------- */
/* ------------------------------------------------- Global variable & Function -------------------------------------------------------------- */
/* ------------------------------------------------------------------------------------------------------------------------------------------- */



static char *heap_listp;        // 항상 가용 블록을 가리키는 정적 전역 변수

static void RemoveFreeBlock(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *first_fit(size_t asize);
static void place(void *bp, size_t asize);

int         mm_init(void);
void        *mm_malloc(size_t size);
void        mm_free(void *bp);



/* ------------------------------------------------------------------------------------------------------------------------------------------ */
/* ------------------------------------------------------Function Code----------------------------------------------------------------------- */
/* ------------------------------------------------------------------------------------------------------------------------------------------ */

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));          // Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));          // Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (4 * WSIZE), NULL);
    PUT(heap_listp + (5 * WSIZE), NULL);
    PUT(heap_listp + (6 * WSIZE), PACK(2 * DSIZE, 1));
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1));              // Epilogue Header -> 왜 size == 0?
    heap_listp += 4 * WSIZE;                                // Prologue block 다음 블록 위치 지정

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void RemoveFreeBlock(void *bp)
{
    if(bp == heap_listp)
    {
        heap_listp = NEXT_FREEBLOCK(bp);
        return;
    }

    NEXT_FREEBLOCK(PREV_FREEBLOCK(bp)) = NEXT_FREEBLOCK(bp);

    if(NEXT_FREEBLOCK(bp) != NULL)
    {
        PREV_FREEBLOCK(NEXT_FREEBLOCK(bp)) = PREV_FREEBLOCK(bp);
    }
}

static void AddFreeBlock(void *bp)
{
    void *tempBp = heap_listp;

    if(tempBp == NULL)
    {
        heap_listp = bp;
        NEXT_FREEBLOCK(heap_listp) = NULL;
        return;
    }

    while(tempBp < bp)
    {
        if(NEXT_FREEBLOCK(tempBp) == NULL || NEXT_FREEBLOCK(tempBp) > bp)
            break;
        tempBp = NEXT_FREEBLOCK(tempBp);
    }

    NEXT_FREEBLOCK(bp) = NEXT_FREEBLOCK(tempBp);
    NEXT_FREEBLOCK(tempBp) = bp;
    PREV_FREEBLOCK(bp) = tempBp;

    if(NEXT_FREEBLOCK(bp) != NULL)
        PREV_FREEBLOCK(NEXT_FREEBLOCK(bp)) = bp;
}

// 가용 블록들을 통합
static void *coalesce(void *bp)
{
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전, 다음 블록이 가용 블록인지 확인해서 통합
    if(prev_alloc && next_alloc)
    {
        AddFreeBlock(bp);
        return bp;
    }

    else if(prev_alloc && !next_alloc)
    {
        RemoveFreeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        AddFreeBlock(bp);
    }

    else if(!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    {
        RemoveFreeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

// 새로운 가용 블록으로 힙 확장
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       // New Epilogue Header

    return coalesce(bp);                        // 힙 영역 확장시 이전 블록 혹은 prologue블록과 epilogue 블록과 연결이 돼있는지 확인?
}

static void *first_fit(size_t asize)
{
    char *tempBp = heap_listp;

    while(tempBp != NULL)
    {
        if(GET_SIZE(HDRP(tempBp)) >= asize)
            return tempBp;
        tempBp = NEXT_FREEBLOCK(tempBp);
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(bp), PACK((csize - asize), 0));

        NEXT_FREEBLOCK(bp) = NEXT_FREEBLOCK(PREV_BLKP(bp));

        if(PREV_BLKP(bp) == heap_listp)
        {
            heap_listp = bp;
        }    
        else
        {
            PREV_FREEBLOCK(bp) = PREV_FREEBLOCK(PREV_BLKP(bp));
            NEXT_FREEBLOCK(PREV_FREEBLOCK(PREV_BLKP(bp))) = bp;
        }

        if(NEXT_FREEBLOCK(bp) != NULL)
            PREV_FREEBLOCK(NEXT_FREEBLOCK(bp)) = bp;
    }
    else
    {
        RemoveFreeBlock(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
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
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}