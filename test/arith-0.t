% Comments :
%------------------------------------------------------------------------------
tff(consta, type,
    a : $int ).

tff(test,conjecture,(
    ~ ! [X : $int]: ( $lesseq($sum(X, X), a) | $lesseq($sum(X,$sum(X,X)),a) )
    )).
%tff(test,conjecture,(
%    ~ ! [X : $int]: ( $lesseq($sum(X, X), a) )
%    )).
%------------------------------------------------------------------------------
