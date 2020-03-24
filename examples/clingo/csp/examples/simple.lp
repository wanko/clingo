%const(5).
%{a}.
%&sum{C-y}=:x :- const(C).
%&sum{x : a}=:z.

%{ a }.
%&min{1;2;3} =: x :- a.
%&sum{x} =: y.
%#show a/0.

&sum{x}=1 :- &sum{ 1 : a }>= 0.
a :- &sum{x}=1.