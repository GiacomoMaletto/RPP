---
output: pdf_document
---

# Reviews follow-up for "Certifying expressive power and algorithms of Reversible Primitive Permutations with LEAN"


## Da fare
Le uniche questioni aperte mi sembrano la 1), 2), 3), 22), quando hai tempo potresti occupartene? Se riesci puoi dare un'occhiata alle mie modifiche su Github, motivate in questa mail.


## Reponse

1. **Observation/Question**
   - abstract, l. 11: I would remove the sentence about the novel contribution from the abstract, if you want you can move it to the intro at lines 93-95 where you discuss the novelty of your paper
  
*Done.* 
We have just dropped the sentence from the abstract. Lines 93-95 already underline how this work extends the one of RC2022.

2. **Observation/Question**
   - p. 1, l. 7-9: do you have any citation to refer to here?
   - p. 2, l. 37: it seems to me you never come back to this. Also, what is the fix-point problem?

*Done.*
References [1], [2], [3], and [4] added (p.1, l.7--8). Statement and meaning of fix-point problem recalled (p.2, l.39--42)

3. **Observation/Question**
   - p. 4, l. 106: in in

*Done.*

4. **Observation/Question**
   - p. 5, fig. 2: please use code font for It (and maybe also f) in the comment, otherwise it seems simple text

*Done.* This is not a simple request: the package `lstlisting` takes under control which font to use and where. We add 'It f' and 'f' in the comment of Fig.2


5. **Observation/Question**
   - p. 5, l. 129: strange space at the beginning of the row

*Done.*


6. **Observation/Question**
   - p. 7, l. 152: is this standard Lean syntax? Or did you defined it?
  
*Done.* See p. 5, l. 153 - 169 where we add a full blown explanation.


7. **Observation/Question**
   
   - p. 7, l. 160: property -> properties

*Done.*


8. **Observation/Question**
   
   - p. 8, l. 197-198: something seems missing here: there is a both followed by a single item, and also the code seems missing something. Indeed, I was expecting an equality (or maybe this is just my poor understanding of Lean)
     
*Done.* See p. 8, l. 214 - 218, starting from sentence "This can be restated ...".
 

9. **Observation/Question**
   
   - p. 8, l. 199: I understand your proof technique (and it is interesting), but could you also have used copy-cat from the previous one?
   
*Done.* See p. 9, l. 222 - 223 for a brief answer.


10. **Observation/Question**
    
    -  p. 9, l. 237: do you miss arguments x0 ... xn-2 ? 

*Done.* See p. 10, l. 260: arguments added.


11.  **Observation/Question**
    
    -  p. 10, l. 260: could you give an intuition about how the general schema works?
       
       -  *G: Penso che il modo migliore per capire come funziona step sia vedere gli esempi, perciò non ho aggiunto nulla.*
       -  *L: Secondo me ci sono due modi per rispondere:*
          -  (Troppo) pesante? Dare una qualche caratterizzazione formale del risultato, ipotizzando una proprietà della funzione che riempie il buco
          -  Più accettabile? Descrivere lo scopo di ciascuno dei blocchi composti in sequenza, avendo la finalità di descrivere cosa si prepara come input del buco, e cosa ci si aspetta che la funzione che riempie il buco produca
       - *G: Si potrebbe fare in questo modo: enunciare la seguente proprietà. "Let f : list Z^{m+2} \to Z^{m+2} be a function such that for all x >= 0, for all z \in Z^m we have that f(x,0,z)=(0,y',z') for some y' >= 0, z' \in Z^m; suppose that x,y >= 0 and that z \in Z^m. Then (step f)(x,y,0,z)=(x+1,y-1,0,z) if y>0 and (0,y',0,z') if y=0 and f(x,0,z)=(0,y',z')." Lo dimostrerei in Lean e aggiungerei anche un diagramma stile figura 9b/c in cui viene mostrato come ogni assunzione sia utilizzata in un passaggio, e in modo che forse i passaggi siano più chiari. Una volta fatta questa descrizione, diventa anche più facile descrivere cp, divisione e radice quadrata: basta spiegare come l'istruzione step scelta si traduce nell'azione che si desidera. Sicuramente è un po' pesante, ma almeno è preciso.* 
 

12. **Observation/Question**
    
    -  p. 13, l. 299 - 302: since it is relevant for your proof you should provide a description
    
       - *G: Non l'ho fatto perché come prima mi sembra che sapere la definizione non serva a molto, ma forse sarebbe effettivamente il caso? Cosa ne pensi?*
       - *L: Né io né te abbiamo voglia di farlo, ma mi sa che ci tocca. Però, secondo me non sta chiedendo la definizione. È piuttosto interessato ad una lettura dell'invariante o a una definizione qualitativa come quella della step(x,y) a p. 13, l. 291. Che ne pensi?*

       - *G: Forse potremmo cavarcela dicendo effettivamente come è definita analiticamente la funzione: in effetti, io ho solo usato la definizione analitica per definirla in Lean, senza cercare un modo geometrico di*


13. **Observation/Question**
    
    -  p. 15, l. 364: why do you require forall z, instead of just using 0 for z?
    
*Because the statement is slightly more general, and it does not substantially increase the complexity of the proof.*


14.  **Observation/Question**

    -  p. 16, Rem. 6: could you provide a general proof, for each pair of
    packing/unpacking functions satisfying some suitable requirements?

*We interpret this question as a curiosity, not as a request to develop a whole formal reasoning in Lean to prove `theorem completeness` (p. 16, l. 395) with the function `cp` in place of `mkpair`. Of course `cp` can replace `mkpair`, because both have the same identical interface. Clearly, the two isomorphisms have a differente graphs (seen as mathematical functions). However the proof of `theorem completeness` does not rely on a specific strategy to encode pairs of numbers into a single value.*


15.  **Observation/Question**
    
    - p. 18, l. 424: need -> needs

*Done.*


## ## FIN QUI ############################


16. **Observation/Question**
  
    -  p. 18, l. 431: if you choose different immersions which differ for some non primitive recursive automorphisms, would you get different notions of encodable? If so, in which sense the one you get is good?

Mi sembra una questione abbastanza interessante, ma non approfondirei troppo. Ho aggiunto una frase.


17.  **Observation/Question**
  
    - p. 19, l. 449: could you clarify why the class mechanism is useful here, and how?

Ho cambiato un po' la frase per mostrare meglio il ruolo delle class.


18. **Observation/Question**
    
    - p. 19, l. 468: are are

*Done.*


19. **Observation/Question**
    
    -  p. 20, l. 499: Lean tactics mode with by refl: this sentence seems ungrammatical; also, could you clarify what is refl?

Ho tolto "by" in "by refl" e specificato meglio a cosa serve la tattica "refl".


19. **Observation/Question**
    
    - p. 21, l. 517: into two steps -> in two steps

*Done.*


20.  **Observation/Question**
    
    - p. 23, l. 587: could you provide a citation for Pendulum ISA?

Non so bene di cosa si tratti, puoi darmi una mano?


21. **Observation/Question**

    - At the end of section 2 the authors claim that It is more primitive, but their arguments are not convincing without having also a definition of It in terms of ItR.

Forse non siamo d'accordo sul significato di "primitivo". Se si potesse esprimere "It" in termini di "ItR", allora sarebbero equivalenti, invece dico che "It" sia più primitivo perché ci puoi esprimere più roba, tra cui "ItR", no?


22. **Observation/Question**
    
    - Line 311. "here " should be removed.

*Done.*


23. **Observation/Question**
    
    - LEAN 4 releases are available (non the stable one). May be a small example with C code could be added.

Mi sono accorto che Lean4 non permette di esportare direttamente codice C, lo utilizza solo internamente. Ho cambiato un po' la frase.