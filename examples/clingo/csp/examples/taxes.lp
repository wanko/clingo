person(peter;paul;mary).
region(luxemburg;germany).
rate(germany,  25000, 15).
rate(germany,  50000, 25).
rate(germany, 100000, 35).
rate(luxemburg,  38700, 14).
rate(luxemburg,  58000, 23).
rate(luxemburg,  96700, 30).
income(peter,  40000).
income(paul,   60000).
income(mary,  120000).
deduction(mary, 10000, 12000).

&sum{ 0 } =: deduction(P) :- person(P), not deduction(P,_,_).
&in{ L..H } =: deduction(P) :- deduction(P,L,H).
rate(P,T) :- lives(P,R), income(P,I),
             T = #max{ T' : rate(R,L,T'), I>=L}.

1 { lives(P,R) : region(R) } 1 :- person(P).

&sum{ T-deduction(P) } =: tax(P) :- income(P,I), rate(P,R),
                                    T=I*R/100.

&sum{ tax(P) : lives(P,R) } =: total(R) :- region(R).

min_taxes(P) :- &min{ tax(P') : person(P') } = tax(P), person(P).
max_taxes(P) :- &max{ tax(P') : person(P') } = tax(P), person(P).
&sum{ 1 : lives(P,R), person(P) } =: inhabitants(R) :- region(R).
