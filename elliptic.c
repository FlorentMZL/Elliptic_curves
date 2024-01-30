#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <openssl/sha.h>
#define MAXBits 300

void handl(int signum)
{
    exit(0);
}

typedef struct
{
    mpz_t x;
    mpz_t y;
} point;
void clearPoint(point *p)
{
    mpz_clear(p->x);
    mpz_clear(p->y);
}
typedef struct
{
    mpz_t a;
    mpz_t b;
    mpz_t n;
} courbeElliptique_Weirestrass;
typedef struct 
{
    mpz_t a;
    mpz_t b; 
    mpz_t n;
}courbeElliptique_Montgomery;

void clearCourbe(courbeElliptique_Weirestrass *c)
{
    mpz_clear(c->a);
    mpz_clear(c->b);
    mpz_clear(c->n);
    
}

int quadratic_residue(mpz_t x,mpz_t q,mpz_t n)
{
    int                        leg;
    mpz_t                        tmp,ofac,nr,t,r,c,b;
    unsigned int            mod4;
    mp_bitcnt_t                twofac=0,m,i,ix;

    mod4=mpz_tstbit(n,0);
    if(!mod4) // must be odd
        return 0;

    mod4+=2*mpz_tstbit(n,1);

    leg=mpz_legendre(q,n);
    if(leg!=1)
        return leg;

    mpz_init_set(tmp,n);

    if(mod4==3) // directly, x = q^(n+1)/4 mod n
        {
        mpz_add_ui(tmp,tmp,1UL);
        mpz_tdiv_q_2exp(tmp,tmp,2);
        mpz_powm(x,q,tmp,n);
        mpz_clear(tmp);
        }
    else // Tonelli-Shanks
        {
        mpz_inits(ofac,t,r,c,b,NULL);

        // split n - 1 into odd number times power of 2 ofac*2^twofac
        mpz_sub_ui(tmp,tmp,1UL);
        twofac=mpz_scan1(tmp,twofac); // largest power of 2 divisor
        if(twofac)
            mpz_tdiv_q_2exp(ofac,tmp,twofac); // shift right

        // look for non-residue
        mpz_init_set_ui(nr,2UL);
        while(mpz_legendre(nr,n)!=-1)
            mpz_add_ui(nr,nr,1UL);

        mpz_powm(c,nr,ofac,n); // c = nr^ofac mod n

        mpz_add_ui(tmp,ofac,1UL);
        mpz_tdiv_q_2exp(tmp,tmp,1);
        mpz_powm(r,q,tmp,n); // r = q^(ofac+1)/2 mod n

        mpz_powm(t,q,ofac,n);
        mpz_mod(t,t,n); // t = q^ofac mod n

        if(mpz_cmp_ui(t,1UL)!=0) // if t = 1 mod n we're done
            {
            m=twofac;
            do
                {
                i=2;
                ix=1;
                while(ix<m)
                    {
                    // find lowest 0 < ix < m | t^2^ix = 1 mod n
                    mpz_powm_ui(tmp,t,i,n); // repeatedly square t
                    if(mpz_cmp_ui(tmp,1UL)==0)
                        break;
                    i<<=1; // i = 2, 4, 8, ...
                    ix++; // ix is log2 i
                    }
                mpz_powm_ui(b,c,1<<(m-ix-1),n); // b = c^2^(m-ix-1) mod n
                mpz_mul(r,r,b);
                mpz_mod(r,r,n); // r = r*b mod n
                mpz_mul(c,b,b);
                mpz_mod(c,c,n); // c = b^2 mod n
                mpz_mul(t,t,c);
                mpz_mod(t,t,n); // t = t b^2 mod n
                m=ix;
                }while(mpz_cmp_ui(t,1UL)!=0); // while t mod n != 1
            }
        mpz_set(x,r);
        mpz_clears(tmp,ofac,nr,t,r,c,b,NULL);
        }

    return 1;
}


char* sha1_of_mpz(mpz_t number) {
    unsigned char hash[SHA_DIGEST_LENGTH];
    char *str_number = mpz_get_str(NULL, 10, number); // Convert mpz_t to string

    SHA1((unsigned char*)str_number, strlen(str_number), (unsigned char*)&hash);

    char *hex_string = malloc(SHA_DIGEST_LENGTH*2+1);
    for (int i = 0; i < SHA_DIGEST_LENGTH; i++)
        sprintf(hex_string + i * 2, "%02x", hash[i]);

    hex_string[SHA_DIGEST_LENGTH*2] = 0;

    free(str_number); // Don't forget to free the allocated string

    return hex_string;
}
void addition_montgomery(point *res, point p, point q, courbeElliptique_Montgomery c ){
    mpz_t alpha; 
    mpz_t suby; 
    mpz_t subx; 
    mpz_t x3; 
    mpz_t y3; 
    mpz_t alphacarre;
    mpz_init(alpha); 
    mpz_init(suby);
    mpz_init(subx);
    mpz_init(x3); 
    mpz_init(y3);
    mpz_init(alphacarre);
    mpz_sub(suby, q.y, p.y); 
    
    if (mpz_cmp_ui(suby,0)<0){
        
        mpz_add(suby, suby, c.n);
    }
    mpz_sub (subx, q.x, p.x);
    if(mpz_cmp_ui(subx, 0)<0){
        mpz_add(subx, subx, c.n);
    }
    mpz_invert(subx, subx, c.n);
    mpz_mul(alpha, suby, subx);//(y2-y1)/(x2-x1)
    mpz_mul(alphacarre, alpha, alpha);
    mpz_mul(x3, alphacarre, c.b);
    mpz_mod(x3, x3, c.n);
    mpz_sub(x3, x3, c.a);
    if (mpz_cmp_ui(x3, 0)<0){
        
        mpz_add (x3, x3, c.n);
    }
    mpz_sub (x3, x3, p.x);
    if (mpz_cmp_ui(x3, 0)<0){
        
        mpz_add (x3, x3, c.n);
    }
    mpz_sub(x3, x3, q.x);
    if (mpz_cmp_ui(x3, 0)<0){
        
        mpz_add (x3, x3, c.n);
    }
    mpz_mod(x3, x3, c.n);

    //y3 : 
    mpz_sub(subx,p.x, x3);
    if(mpz_cmp_ui(subx, 0)<0){
        
        mpz_add(subx, subx, c.n);
    }
    mpz_mul(y3, subx, alpha);
    mpz_sub(y3, y3, p.y);
    if (mpz_cmp_ui(y3, 0)<0){
        
        mpz_add(y3,y3, c.n);
    }
    mpz_mod(y3, y3, c.n);
    mpz_set(res->x, x3);
    mpz_set(res->y, y3);
  

}
void doubling_montgomery(point p, courbeElliptique_Montgomery c, point *res){
    mpz_t alpha; 
    mpz_t alphacarre; 
    mpz_t x3; 
    mpz_t y3; 
    mpz_t x1carre; 
    mpz_t by12;
    mpz_t ax12;
    mpz_init(alpha); 
    mpz_init(alphacarre); 
    mpz_init(x3);
    mpz_init(y3);
   
    mpz_init(x1carre);
    mpz_init(by12);
    mpz_init(ax12);
    //calculating 3(x_1^2)    
    mpz_mul(x1carre, p.x, p.x); 
    mpz_mod(x1carre, x1carre, c.n);
    mpz_mul_ui(x1carre, x1carre,3 );
    mpz_mod(x1carre, x1carre, c.n);
    //
    //calculating 2Ax_1
    mpz_mul_ui(ax12, p.x, 2);
    mpz_mul(ax12, c.a, ax12);
    mpz_mod(ax12, ax12, c.n);
    //

    //calculating alpha = 3(x_1^2) + 2Ax_1 + 1 / 2By_1
    //numerator
    mpz_add(alpha, ax12, x1carre);
    mpz_add_ui(alpha,alpha, 1 );
    mpz_mod(alpha, alpha, c.n);
    //
    //denominator
    
    mpz_mul (by12, p.y, c.b);
    mpz_mul_ui(by12, by12, 2);
    
    
    mpz_mod(by12, by12, c.n);
    mpz_invert(by12, by12, c.n);
    mpz_mul(alpha, alpha, by12);
    
    //
    //calculating x3 : 
    //calculating balpha^2 
    mpz_mul(x3, alpha, alpha) ; 
    mpz_mod(x3, x3, c.n);
    mpz_mul(x3, x3, c.b);
    mpz_mod(x3, x3, c.n);
    //

    mpz_sub (x3, x3, c.a); 
    if (mpz_cmp_ui(x3, 0)<0){
        
        mpz_add(x3, x3, c.n);
    }
    //calculating 2x1
    mpz_mul_ui(alphacarre, p.x,2); 
    //

    mpz_sub(x3, x3, alphacarre);
    if (mpz_cmp_ui(x3, 0)<0){
        
        mpz_add(x3, x3, c.n);
    }
    mpz_mod (x3, x3, c.n);


    //y3 

    mpz_sub (alphacarre, p.x, x3); 
    if (mpz_cmp_ui(alphacarre, 0)<0){
        
        mpz_add(alphacarre, alphacarre, c.n);
    }
    mpz_mul(alphacarre, alphacarre, alpha);
    mpz_mod(alphacarre, alphacarre, c.n);
    mpz_sub(alphacarre, alphacarre, p.y);
    if (mpz_cmp_ui(alphacarre, 0)<0){
        
        mpz_add(alphacarre, alphacarre, c.n);
    }
    mpz_set(y3, alphacarre);
    mpz_set(res->x, x3); 
    mpz_set (res->y, y3);
    
}


void addition(point *res2, point p1, point p2, courbeElliptique_Weirestrass c)
{
    //make sure res is initialized before using this
    if (mpz_cmp_si(p1.x, 0) == 0 && mpz_cmp_si(p1.y, 0) == 0)
    {

        mpz_set(res2->x, p2.x);
        mpz_set(res2->y, p2.y);
        return;
    }
    if (mpz_cmp_si(p2.x, 0) == 0 && mpz_cmp_si(p2.y, 0) == 0)
    {
        mpz_set(res2->x, p1.x);
        mpz_set(res2->y, p1.y);
        return;
    }

    mpz_t pgcd;
    mpz_init(pgcd);
    mpz_t sub;
    mpz_init(sub);
    mpz_sub(sub, p1.x, p2.x);
    mpz_mod(sub, sub, c.n);

    mpz_gcd(pgcd, sub, c.n);
    // gmp_printf("pgcd 1 : %Zd\n", pgcd);
    // gmp_printf("pgcd : %Zd\n", pgcd);
    if (mpz_cmp_d(pgcd, 1) == 0)
    {
        mpz_t lambda;
        mpz_init(lambda);
        mpz_t x3;
        mpz_t y3;
        mpz_init(x3);
        mpz_init(y3);

        mpz_invert(lambda, sub, c.n);
        mpz_sub(sub, p1.y, p2.y);
        mpz_mod(sub, sub, c.n);
        mpz_mul(lambda, sub, lambda);
        mpz_mod(lambda, lambda, c.n);
        mpz_mul(sub, lambda, lambda);
        mpz_mod(sub, sub, c.n);
        mpz_sub(sub, sub, p1.x);
        mpz_mod(sub, sub, c.n);
        mpz_sub(x3, sub, p2.x);
        mpz_mod(x3, x3, c.n);
        mpz_sub(sub, p1.x, x3);
        mpz_mod(sub, sub, c.n);
        mpz_mul(sub, sub, lambda);
        mpz_mod(sub, sub, c.n);
        mpz_sub(y3, sub, p1.y);
        mpz_mod(y3, y3, c.n);
        mpz_set(res2->x, x3);
        mpz_set(res2->y, y3);
        mpz_clear(sub);
        mpz_clear(pgcd);

        mpz_clear(lambda);
        mpz_clear(x3);
        mpz_clear(y3);

        return;
    }
    else if (mpz_cmp(pgcd, c.n) == 0)
    {

        mpz_add(sub, p1.y, p2.y);

        mpz_mod(sub, sub, c.n);
        mpz_gcd(pgcd, sub, c.n);

        if (mpz_cmp_d(pgcd, 1) != 0 && mpz_cmp(pgcd, c.n) != 0)
        {
            printf("FACTEUR TROUVE\n");
            mpz_clear(pgcd);
            // gmp_printf("valide = %Zd", *valide);
            mpz_clear(sub);
            mpz_set(res2->x, p1.x);
            mpz_set(res2->y, p1.y);
            return;
        }
        if (mpz_cmp(pgcd, c.n) == 0)
        {
            // printf("pgcd(y) egal a n\n ")

            mpz_clear(pgcd);
            mpz_clear(sub);
            mpz_set_si(res2->x, 0);
            mpz_set_si(res2->y, 0);
            return;
        }
        if (mpz_cmp_d(pgcd, 1) == 0)
        {

            // printf("pgcd(y) egal a 1\n");
            mpz_t lambda;
            mpz_t lambdacarre;
            mpz_init(lambdacarre);
            mpz_t x3;
            mpz_t y3;
            mpz_init(y3);
            mpz_init(x3);
            mpz_init(lambda);
            mpz_mul(lambda, p1.x, p1.x);   // x^2
            mpz_mod(lambda, lambda, c.n);  // mod n
            mpz_mul_ui(lambda, lambda, 3); // 3x^2

            mpz_mod(lambda, lambda, c.n);

            mpz_add(lambda, lambda, c.a);

            mpz_invert(sub, sub, c.n);

            mpz_mul(lambda, sub, lambda);

            mpz_mod(lambda, lambda, c.n);
            mpz_mul(lambdacarre, lambda, lambda);

            mpz_sub(sub, lambdacarre, p1.x);
            mpz_sub(sub, sub, p2.x);
            mpz_mod(sub, sub, c.n);
            mpz_set(x3, sub);

            mpz_sub(sub, p1.x, x3);

            mpz_mul(sub, sub, lambda);

            mpz_mod(sub, sub, c.n);

            mpz_sub(sub, sub, p1.y);

            mpz_mod(sub, sub, c.n);
            mpz_set(res2->x, x3);
            mpz_set(res2->y, sub);
            mpz_clear(lambda);
            mpz_clear(sub);
            mpz_clear(x3);
            mpz_clear(y3);
            mpz_clear(pgcd);
            mpz_clear(lambdacarre);
            return;
        }
    }
    else
    {
        printf("FACTEUR 2 ");
        mpz_clear(pgcd);
        mpz_clear(sub);
        mpz_set(res2->x, p1.x);
        mpz_set(res2->y, p1.y);
        return;
    }
}
void buildCurve_weirestrass(courbeElliptique_Weirestrass *c, mpz_t n,mpz_t b ,mpz_t a){
    mpz_init_set(c->a, a);
    mpz_init_set (c->n, n);
    mpz_init_set (c->b, b);
}
void buildcurve_montgomery(courbeElliptique_Montgomery* c, mpz_t n, mpz_t b, mpz_t a){
    mpz_init_set(c->a, a);
    mpz_init_set (c->n, n);
    mpz_init_set (c->b, b);
}
int racinecaree(int nb)
{
    int i = 0;
    while (i * i < nb)
    {
        i++;
    }
    return i;
}
int expbinaire(int nb, int puissance)
{
    int res = 1;
    while (puissance > 0)
    {
        if (puissance % 2 == 1)
        {
            res = res * nb;
        }
        nb = nb * nb;
        puissance = puissance / 2;
    }
    return res;
}
void bonnepuissance(mpz_t *res, mpz_t nb, mpz_t borne)
{
    mpz_t anciennb;
    mpz_init(anciennb);
    mpz_set(anciennb, nb);
    // gmp_printf("appel de bonnepuissance sur nb = %Zd, borne = %Zd\n", nb, borne);
    mpz_t nbmul;
    mpz_init(nbmul);
    mpz_set(nbmul, nb);
    mpz_t nb2;
    mpz_init(nb2);
    mpz_sqrt(nb2, borne);
    mpz_mul_ui(nb2, nb2, 2);
    mpz_add_ui(nb2, nb2, 1);
    mpz_add(nb2, borne, nb2);
    while (mpz_cmp(nb, nb2) < 0)
    {
        mpz_mul(nb, nbmul, nb);
        //  gmp_printf("nombre = %Zd\n, borne = %Zd\n", nb, nb2);
    }
    if (mpz_cmp(nb, borne) > 0)
    {
        mpz_div(nb, nb, nbmul);
    }
    mpz_set(*res, nb);
    mpz_set(nb, anciennb);
    mpz_clear(anciennb);
    mpz_clear(nb2);
    mpz_clear(nbmul);
    // gmp_printf("res = %Zd\n", *res);
}
int degreeBin(mpz_t nb)
{
    return mpz_sizeinbase(nb, 2);
}
void multiplication(point *res1, point p1, mpz_t k, courbeElliptique_Weirestrass c)
{ // Multiplication de p1 par k, meme principe que l'exponentiation binaire

    point res;
    mpz_init(res.x);
    mpz_init(res.y);
    mpz_set_d(res.x, 0);
    mpz_set_d(res.y, 0);
    point ad;
    mpz_init(ad.x);
    mpz_init(ad.y);
    mpz_set(ad.x, p1.x);
    mpz_set(ad.y, p1.y);
    for (size_t i = 0; i < mpz_sizeinbase(k, 2); i++)
    {
        if (mpz_tstbit(k, i) == 1)
        {
            addition(&res, res, ad, c);
            addition(&ad, ad, ad, c);
        }
        else
        {
            addition(&ad, ad, ad, c);
        }
    }

    mpz_set(res1->x, res.x);
    mpz_set(res1->y, res.y);
    clearPoint(&res);
    clearPoint(&ad);
}


void montgomery_multiplication(point* res, point p,mpz_t k, courbeElliptique_Montgomery c){
    point r0; 
    point r1; 
    point temp; 
    point temp2; 
    mpz_init(temp2.x);
    mpz_init(temp2.y);
    mpz_init(temp.x); 
    mpz_init(temp.y);
    mpz_init(r0.x);
    mpz_init (r0.y);
    mpz_init(r1.x);
    mpz_init(r1.y);
    mpz_set(r0.x, p.x);
    mpz_set(r0.y, p.y);
    doubling_montgomery(p, c, &r1);
    size_t numbits = mpz_sizeinbase(k,2)-1;
    for (size_t i =  0; i<numbits; i++)
    {   size_t bit_index = numbits -i-1;
        if (mpz_tstbit(k, bit_index) == 1)
        {
            addition_montgomery(&r0, r0,r1, c);
            doubling_montgomery(r1,c,&r1);
        }
        else
        {
            addition_montgomery(&r1, r0, r1, c); 
            doubling_montgomery(r0,c,&r0);           
        }
    }
    mpz_set(res->x, r0.x); 
    mpz_set(res->y,r0.y );

}

void y_from_x_montgomery(mpz_t* y, mpz_t x, courbeElliptique_Montgomery c){
    mpz_t cube; 
    mpz_t carre; 
    mpz_t res; 
    mpz_inits(cube, carre,res); 
    mpz_mul(carre, x, x);
    mpz_mod(carre,carre, c.n);
    mpz_mul(cube, carre, x);
    mpz_mod(cube, cube, c.n);
    mpz_mul(carre, carre,c.a );
    mpz_mod(carre, carre, c.n);
    mpz_add (cube, x, cube);
    mpz_mod(cube, cube, c.n);
    mpz_add(res, cube, carre);
    mpz_mod(res, res, c.n);
    mpz_t realres ; 
    mpz_init(realres);
    quadratic_residue(realres, res, c.n);
    mpz_set(*y, realres);
    
    mpz_mul(realres, realres, realres);
    mpz_mod(realres, realres, c.n);

    mpz_mul(carre, x, x);
    mpz_mul(cube, carre, x);
    mpz_mod(cube, cube, c.n);
    mpz_mul(carre, carre, c.a);
    mpz_add (cube, cube, carre);
    mpz_add (cube, cube, x);
    if (mpz_cmp(cube, realres)!=0){
        printf("PROBLEME\n");
    }

}



void y_from_x_weirestrass(mpz_t* y, mpz_t x, courbeElliptique_Weirestrass  c){
//y must be already initialized 
//we assume that p =3mod4 
    mpz_t cube; 
    mpz_t qns; 
    mpz_init_set_d(qns, 0);
    mpz_mul(qns, x, c.a);
    mpz_mod(qns, qns, c.n);
    mpz_init_set_d(cube, 0); 
    mpz_mul(cube, x, x); 
    mpz_mod(cube, cube, c.n); 
    mpz_mul (cube, cube, x);
    mpz_mod(cube, cube, c.n); 
    mpz_add(cube, cube, qns);
    mpz_add(cube, cube, c.b);
    mpz_mod(cube, cube, c.n);
    mpz_set(*y, cube);
    mpz_mod(*y, *y, c.n);
    mpz_t exp; 
    mpz_t pp1; 
    mpz_init(exp);
    mpz_init(pp1); 
    mpz_add_ui(pp1, c.n, 1);
    mpz_div_ui(pp1, pp1, 4);  
    mpz_powm(exp,*y,pp1,c.n);
    mpz_set(*y,exp);
    

    
}

int main()
{   
    mpz_t p1; 
    mpz_init_set_ui(p1, 2); 
    mpz_pow_ui(p1, p1, 255);
    mpz_sub_ui(p1, p1, 19);
    courbeElliptique_Montgomery c;
    mpz_t n; 
    mpz_init_set(n,p1);
    mpz_t b ; 
    mpz_init_set_ui(b, 1);
    mpz_t a; 
    mpz_init_set_str(a, "486662", 10);
    buildcurve_montgomery(&c, n, b, a);
    gmp_printf("builded curve :  a= %Zd, b = %Zd, n = %Zd\n", c.a, c.b, c.n);
    point p;     
    point r; 
    mpz_init (r.x);
    mpz_init(r.y);
    mpz_init_set_ui(p.x, 9);
    mpz_init(p.y);
    y_from_x_montgomery(&p.y, p.x, c);
    mpz_t k ; 
    mpz_init_set_ui(k, 0x1337c0decafe);
    montgomery_multiplication(&r, p, k, c);
    gmp_printf("multiplication result : x = %Zd, y = %Zd\n", r.x, r.y);
   
    /*y_from_x_montgomery(&p.y, p.x, c);
    gmp_printf(" found y = %Zd\n", p.y);
    point res ; 
    mpz_init(res.x);
    mpz_init(res.y);
    mpz_t k; 
    mpz_init_set_ui(k, 0x1337c0decafe);
    gmp_printf("k = %Zd\n", k);
    montgomery_multiplication(&res , p, k, c);
    gmp_printf("multiplication result : x = %Zd, y = %Zd\n", res.x, res.y);
    point aa ;
    mpz_init(aa.x);
    mpz_init(aa.y);
    point bb;
    mpz_init(bb.x);
    mpz_init(bb.y);
    point cc;
    mpz_init(cc.x);
    mpz_init(cc.y);
    mpz_set_ui(aa.x, 9 );
    y_from_x_montgomery(&aa.y, aa.x, c);
    doubling_montgomery(aa, c, &bb);
    gmp_printf("doubling result : x = %Zd, y = %Zd\n", bb.x, bb.y);
    mpz_set(cc.x,aa.x );
    mpz_set(cc.y, aa.y);
    
    doubling_montgomery(cc, c, &cc);
    gmp_printf("doubling result : x = %Zd, y = %Zd\n", cc.x, cc.y);
*/
}