-*
1/(1-q^2*zbar) * matrix {{1 - q^2*zbar, 0, 0, 0, 0, 0, 0, -((-1 + q)*(1 + q)*zbar), 0}, {0, 0, 0, 1 - q^2*zbar, 0, 0, 0, 0,
        ((-1 + q)*(1 + q)*zbar)/q}, {0, 0, 0, 0, 0, 0, -(q*(-1 + zbar)), 0, 0}, {0, -(q*(-1 + zbar)), 0, 0, 0, 0, 0, 0, 0},
    {0, 0, -((-1 + q)*(1 + q)*zbar), 0, 1 - q^2*zbar, 0, 0, 0, 0}, {-((-1 + q)*(1 + q)), 0, 0, 0, 0, 0, 0, 1 - q^2*zbar, 0},
    {0, 0, 1 - q^2*zbar, 0, -((-1 + q)*(1 + q)), 0, 0, 0, 0}, {0, 0, 0, 0, 0, -(q*(-1 + zbar)), 0, 0, 0},
    {0, 0, 0, (-1 + q)*q*(1 + q), 0, 0, 0, 0, 1 - q^2*zbar}};
*-
q ->
(
    hashTable{("0","0","0") => 1,("0","1","10") => 1,("1","1","1") => 1,("1","10","0") => -q,("10","0","1") => -q,("10","10","10") => -q},
    hashTable{("0","0","0") => 1,("0","1","10") => 1,("1","1","1") => 1,("1","10","0") => -1/q,("10","0","1") => -1/q,("10","10","10") => -1/q}
    )