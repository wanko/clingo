def(#($\mathit{min}$#)) :- def(#($x_1$)#),#(\dots#),def(#($x_n$)#).
:- not &sum(body){$\mathit{min}$} <= $e_i$.
s :- sum(body){$\mathit{min}$} = $e_i$.
:- not s, def(#($\mathit{min}$#)).