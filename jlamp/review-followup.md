# Reviews follow-up for "Certifying expressive power and algorithms of Reversible Primitive Permutations with LEAN"


## Da fare
Le uniche questioni aperte mi sembrano la 1), 2), 3), 22), quando hai tempo potresti occupartene? Se riesci puoi dare un'occhiata alle mie modifiche su Github, motivate in questa mail.


## Reponse

**Observation/Question**
1. abstract, l. 11: I would remove the sentence about the novel contribution from the abstract, if you want you can move it to the intro at lines 93-95 where you discuss the novelty of your paper

*Done* We have just dropped the sentence from the abstract. Lines 93-95 already underline how this work extends the one of RC2022.

**Observation/Question**
2. p. 1, l. 7-9: do you have any citation to refer to here?
3. p. 2, l. 37: it seems to me you never come back to this. Also, what is the fix-point problem?

*Done* References [1], [2], [3], and [4] added (p.1, l.7--8). Statement and meaning of fix-point problem recalled (p.2, l.39--42)

**Observation/Question**
4. p. 4, l. 106: in in

*Done*

**Observation/Question**
5. p. 5, fig. 2: please use code font for It (and maybe also f) in the comment, otherwise it seems simple text

*Does* This is not a simple request: the package `lstlisting` takes under control which font to use and where. We add 'It f' and 'f' in the comment of Fig.2


**Observation/Question**
6. p. 5, l. 129: strange space at the beginning of the row

*Done*


## FIN QUI



**Observation/Question**
7. p. 7, l. 152: is this standard Lean syntax? Or did you defined it?

Ho cercato di chiarire la faccenda allungando la frase.


**Observation/Question**
8. p. 7, l. 160: property -> properties

Corretto.


**Observation/Question**
9. p. 8, l. 197-198: something seems missing here: there is a both followed by a single item, and also the code seems missing something. Indeed, I was expecting an equality (or maybe this is just my poor understanding of Lean)

In effetti la frase non aveva senso, l'ho riscritta.

**Observation/Question**
10.   p. 8, l. 199: I understand your proof technique (and it is interesting), but could you also have used copy-cat from the previous one?

Ho scritto che si potrebbe anche ricopiare la tecnica dimostrativa usata precedentemente, ma a costo di avere molte ripetizioni.


**Observation/Question**
11.  p. 9, l. 237: do you miss arguments x0 ... xn-2 ? 

Penso abbia ragione, gli ho aggiunti.


**Observation/Question**
1.   p. 10, l. 260: could you give an intuition about how the general schema works?

Penso che il modo migliore per capire come funziona step sia vedere gli esempi, perciò non ho aggiunto nulla.
 

**Observation/Question**
13. p. 13, l. 209-302: since it is relevant for your proof you should provide a description

Non l'ho fatto perché come prima mi sembra che sapere la definizione non serva a molto, ma forse sarebbe effettivamente il caso? Cosa ne pensi?


**Observation/Question**
14.  p. 15, l. 364: why do you require forall z, instead of just using 0 for z?

15.  p. 16, Rem. 6: could you provide a general proof, for each pair of
    packing/unpacking functions satisfying some suitable requirements?

Non mi sembrano questioni molto importanti, non ho cambiato nulla.


**Observation/Question**
16. p. 18, l. 424: need -> needs

Corretto.


**Observation/Question**
17. p. 18, l. 431: if you choose different immersions which differ for some non primitive recursive automorphisms, would you get different notions of encodable? If so, in which sense the one you get is good?

Mi sembra una questione abbastanza interessante, ma non approfondirei troppo. Ho aggiunto una frase.


**Observation/Question**
18.   p. 19, l. 449: could you clarify why the class mechanism is useful here, and how?

Ho cambiato un po' la frase per mostrare meglio il ruolo delle class.


**Observation/Question**
19. p. 19, l. 468: are are

Corretto.


**Observation/Question**
20. p. 20, l. 499: Lean tactics mode with by refl: this sentence seems ungrammatical; also, could you clarify what is refl?

Ho tolto "by" in "by refl" e specificato meglio a cosa serve la tattica "refl".


**Observation/Question**
21.  p. 21, l. 517: into two steps -> in two steps

Corretto.


**Observation/Question**
22. p. 23, l. 587: could you provide a citation for Pendulum ISA?

Non so bene di cosa si tratti, puoi darmi una mano?


**Observation/Question**
23. At the end of section 2 the authors claim that It is more primitive, but their arguments are not convincing without having also a definition of It in terms of ItR.

Forse non siamo d'accordo sul significato di "primitivo". Se si potesse esprimere "It" in termini di "ItR", allora sarebbero equivalenti, invece dico che "It" sia più primitivo perché ci puoi esprimere più roba, tra cui "ItR", no?


**Observation/Question**
24. Line 311. "here " should be removed.

Corretto.


**Observation/Question**
25. LEAN 4 releases are available (non the stable one). May be a small example with C code could be added.

Mi sono accorto che Lean4 non permette di esportare direttamente codice C, lo utilizza solo internamente. Ho cambiato un po' la frase.
