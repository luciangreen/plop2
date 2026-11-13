% An integer input: plop2 formula finds a closed form for each position.
% letter(N, Out): Out = [the N-th letter after a, '-', x].
letter(N, [C, '-', x]) :- Code is 0'a + N, char_code(C, Code).

% Squares as text: char 1 of "<N*N>" ...
square(N, Out) :- S is N * N, number_codes(S, Cs), atom_codes(A, Cs), atom_chars(A, Chars),
    append(Chars, [';'], Out).
