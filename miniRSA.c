/*
 * @file    rsa.c
 * @author  구수연 / 2014037756
 * @date    2017.11.26
 * @brief   mini RSA implementation code
 * @details 세부 설명
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "miniRSA.h"
#include <math.h>

uint p, q, e, d, n;
uint GCD(uint a, uint b);

uint mod(uint x, uint p){
	uint tp = p;
	
	if(p == 2)
		return x&1;
	
	while(tp < x) //자리수 맞추기
		tp = tp<<1;
		
	while(tp >= p){ //나누기
		if(x >= tp)
			x = x^tp;
		tp = tp>>1;
	}
	
	return x;
}

/*
 * @brief     모듈러 덧셈 연산을 하는 함수.
 * @param     uint a     : 피연산자1.
 * @param     uint b     : 피연산자2.
 * @param     byte op    : +, - 연산자.
 * @param     uint n      : 모듈러 값.
 * @return    uint result : 피연산자의 덧셈에 대한 모듈러 연산 값. (a op b) mod n
 * @todo      모듈러 값과 오버플로우 상황을 고려하여 작성한다.
 */
uint ModAdd(uint a, uint b, byte op, uint n) {
	uint result=0;
	a = mod(a,n);
	b = mod(b,n);
	
	switch(op){
        case '+':
				if(b == 0){
					result = a;
				} else {
					b = n-b;
					if(a >= b)
						result = mod(a-b,n);
					else
						result = mod(a-b+n,n);
				}
        case '-':
				if(a >= b){
					result = mod(a-b,n);
				} else {
					result = mod(a-b+n,n);
				}			
	}
	
    return result;
}

/*
 * @brief      모듈러 곱셈 연산을 하는 함수.
 * @param      uint x       : 피연산자1.
 * @param      uint y       : 피연산자2.
 * @param      uint n       : 모듈러 값.
 * @return     uint result  : 피연산자의 곱셈에 대한 모듈러 연산 값. (a x b) mod n
 * @todo       모듈러 값과 오버플로우 상황을 고려하여 작성한다.
 */
uint ModMul(uint x, uint y, uint n) {
	uint result=0;
	
	x = mod(x,n);
	y = mod(y,n);
	
	while(y){
		if(mod(y,2) == 1)
			result = ModAdd(result,x,'+',n);
		
		y = y>>1;
		
		if(x < ModAdd(n,x,'-',n))
			x = x<<1;
		else
			x = ModAdd(x,ModAdd(n,x,'-',n),'-',n);
	}
    
    return result;
}

/*
 * @brief      모듈러 거듭제곱 연산을 하는 함수.
 * @param      uint base   : 피연산자1.
 * @param      uint exp    : 피연산자2.
 * @param      uint n      : 모듈러 값.
 * @return     uint result : 피연산자의 연산에 대한 모듈러 연산 값. (base ^ exp) mod n
 * @todo       모듈러 값과 오버플로우 상황을 고려하여 작성한다.
               'square and multiply' 알고리즘을 사용하여 작성한다.
 */
uint ModPow(uint base, uint exp, uint n) {
	uint result=1;
	base = mod(base,n);
	
	while(exp > 0){
		if(exp & 1)
			result = mod(ModMul(result,base,n),n);
		
		exp = exp>>1;
		base = mod(ModMul(base,base,n),n);
	}
    
    return result;
}

/*
 * @brief      입력된 수가 소수인지 입력된 횟수만큼 반복하여 검증하는 함수.
 * @param      uint testNum   : 임의 생성된 홀수.
 * @param      uint repeat    : 판단함수의 반복횟수.
 * @return     uint result    : 판단 결과에 따른 TRUE, FALSE 값.
 * @todo       Miller-Rabin 소수 판별법과 같은 확률적인 방법을 사용하여,
               이론적으로 4N(99.99%) 이상 되는 값을 선택하도록 한다. 
 */
bool IsPrime(uint testNum, uint repeat) {
	uint k=0, twokq=testNum-1, a;
	
	while(mod(twokq,2) == 0){
		twokq = twokq>>1;
		k++;
	}
	
	for(;repeat>0;repeat--){
		printf("TEST -- %u (%ust)\n",testNum,(uint)11-repeat);
		a = (uint) (WELLRNG512a()*(testNum-2)+2);
		
		if(GCD(a,testNum) != 1)
			return 0;
		
		if(ModPow(a,twokq,testNum)==1 || ModPow(a,twokq,testNum)==testNum-1)
			continue;
		
		if(ModMul(ModPow(a,twokq,testNum), ModPow(a,twokq,testNum), testNum) != testNum-1)
			return 0;
	}
	
	return 1;
}

/*
 * @brief       모듈러 역 값을 계산하는 함수.
 * @param       uint a      : 피연산자1.
 * @param       uint m      : 모듈러 값.
 * @return      uint result : 피연산자의 모듈러 역수 값.
 * @todo        확장 유클리드 알고리즘을 사용하여 작성하도록 한다.
 */
uint ModInv(uint a, uint m) {
	uint z;
	uint x1, x2=a, x3=m;
	uint y1, y2=0, y3=1;
 
	while (x2 != 1)
	{
		z = x3/x2;
		x1 = ModAdd(x3, ModMul(x2,z,m),'-',m);
		y1 = ModAdd(y2, ModMul(y3,z,m),'-',m);
		
		x3 = x2;
		x2 = x1;
		
		y2 = y3;
		y3 = y1;
	}
	
	return y3;
}

/*
 * @brief     RSA 키를 생성하는 함수.
 * @param     uint *p   : 소수 p.
 * @param     uint *q   : 소수 q.
 * @param     uint *e   : 공개키 값.
 * @param     uint *d   : 개인키 값.
 * @param     uint *n   : 모듈러 n 값.
 * @return    void
 * @todo      과제 안내 문서의 제한사항을 참고하여 작성한다.
 */
void miniRSAKeygen(uint *p, uint *q, uint *e, uint *d, uint *n) {
	*p = (uint) (pow(2,15) + WELLRNG512a() * pow(2,15));
	*q = (uint) (pow(2,31)/ *p + WELLRNG512a() * pow(2,31)/ *p);
	
	while(*p==1 || (*p&1)==0 || IsPrime(*p,(uint)10)==0)
		*p = (uint) (pow(2,15) + WELLRNG512a() * pow(2,15));
	printf("*** Prime Num \'p\' is %u\n\n",*p);
		
	while(*q==1 || (*q&1) == 0 || IsPrime(*q,(uint)10)==0)
		*q = (uint) (pow(2,31)/ *p + WELLRNG512a() * pow(2,31)/ *p);
	printf("*** Prime Num \'q\' is %u\n\n",*q);
		
	uint N = (*p-1)*(*q-1);
	*n = (*p)*(*q);
	*e = (uint)(1 + (WELLRNG512a()*N));
	
	printf("*** Testing \'e\' from \'N\'(%u)\n",N);
	while(GCD(*e,N) != 1)
		*e = (uint)(1 + (WELLRNG512a()*N));
		
	*d = ModInv(*e,N);
}

/*
 * @brief     RSA 암복호화를 진행하는 함수.
 * @param     uint data   : 키 값.
 * @param     uint key    : 키 값.
 * @param     uint n      : 모듈러 n 값.
 * @return    uint result : 암복호화에 결과값
 * @todo      과제 안내 문서의 제한사항을 참고하여 작성한다.
 */
uint miniRSA(uint data, uint key, uint n) {
	uint result;
	result = ModPow(data, key, n);
	
    return result;
}

uint GCD(uint a, uint b) {
    uint prev_a;

    while(b != 0) {
        printf("GCD(%u, %u)\n", a, b);
        prev_a = a;
        a = b;
        while(prev_a >= b) prev_a -= b;
        b = prev_a;
    }
    printf("GCD(%u, %u)\n\n", a, b);
    return a;
}

int main(int argc, char* argv[]) {
    byte plain_text[4] = {0x12, 0x34, 0x56, 0x78};
    uint plain_data, encrpyted_data, decrpyted_data;
    uint seed = time(NULL);

    memcpy(&plain_data, plain_text, 4);

    // 난수 생성기 시드값 설정
    seed = time(NULL);
    InitWELLRNG512a(&seed);

    // RSA 키 생성
    miniRSAKeygen(&p, &q, &e, &d, &n);
    printf("0. Key generation is Success!\n ");
    printf("p : %u\n q : %u\n e : %u\n d : %u\n N : %u\n\n", p, q, e, d, n);

    // RSA 암호화 테스트
    encrpyted_data = miniRSA(plain_data, e, n);
    printf("1. plain text : %u\n", plain_data);    
    printf("2. encrypted plain text : %u\n\n", encrpyted_data);

    // RSA 복호화 테스트
    decrpyted_data = miniRSA(encrpyted_data, d, n);
    printf("3. cipher text : %u\n", encrpyted_data);
    printf("4. Decrypted plain text : %u\n\n", decrpyted_data);

    // 결과 출력
    printf("RSA Decryption: %s\n", (decrpyted_data == plain_data) ? "SUCCESS!" : "FAILURE!");

    return 0;
}
