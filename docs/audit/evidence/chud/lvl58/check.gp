default(realprecision, 600);
Psi = read("psi29.txt");
Tf(t) = my(r = (eta(t,1)/eta(2*t,1))^24); r + 24 + 4096/r;
t = 0.13 + 0.31*I;
v = substvec(Psi, [X, Y], [Tf(t), Tf(29*t)]);
s = substvec(Psi, [X, Y], [abs(Tf(t)), abs(Tf(29*t))]);
print("relative |Psi(T(t),T(29t))| = ", abs(v) / vecmax(apply(abs, [Tf(t), Tf(29*t)]))^30 * 1.0);
t58 = I*sqrt(58)/2; print("T(tau58) - T0 = ", Tf(t58) - (256*99^4 - 104));
