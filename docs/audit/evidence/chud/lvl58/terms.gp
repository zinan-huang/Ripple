\\ Psi_29 as (coeff, xPow, yPow) lines, sorted by xPow.
Psi = read("psi29.txt");
system(": > psi29.tsv");
for (x = 0, 30, my(c = polcoeff(Psi, x, X)); for (y = 0, 30, my(v = polcoeff(c, y, Y)); if (v, write("psi29.tsv", v, "\t", x, "\t", y))));
