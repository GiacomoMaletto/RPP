Require Import Unicode.Utf8 List ZArith.
Import ListNotations.
Require Import splice.
Set Implicit Arguments.

(* /// Definizioni di base di RPP /// *)

(* Differenza: per convenienza Id ha come argomento un numero naturale che ne indica l'arietà; in questo modo è anche possibile definire una RPP con arietà nulla, il che è utile in certe definizioni *)

Inductive RPP :=
  | Id (n : nat)
  | Ne
  | Su
  | Pr
  | Sw
  | Co (f g : RPP)
  | Pa (f g : RPP)
  | It (f : RPP)
  | If (f g h : RPP).

Notation "f ;; g" := (Co f g) (at level 66, left associativity).
(* \Vert ‖ *)
Notation "f ‖ g" := (Pa f g) (at level 65, left associativity).

Fixpoint inv f :=
  match f with
  | Id n => Id n
  | Ne => Ne
  | Su => Pr
  | Pr => Su
  | Sw => Sw
  | Co f g => Co (inv g) (inv f)
  | Pa f g => Pa (inv f) (inv g)
  | It f => It (inv f)
  | If f g h => If (inv f) (inv g) (inv h)
  end.

(* Differenza: è possibile comporre funzioni di arietà diverse (ma nella pratica ciò non cambia nulla). *)

Fixpoint arity f :=
  match f with
  | Id n => n
  | Ne => 1
  | Su => 1
  | Pr => 1
  | Sw => 2
  | Co f g => max (arity f) (arity g)
  | Pa f g => arity f + arity g
  | It f => S (arity f)
  | If f g h => S (max (arity f) (max (arity g) (arity h)))
  end.

Fixpoint iter X (f : X → X) (n : nat) x :=
  match n with
  | 0 => x
  | S n => f (iter f n x)
  end.

(* Differenza: It e If non controllano l'ultimo elemento ma il primo. Questo rende i calcoli e le dimostrazioni più semplici *)

(* Differenza/Nota: It non fa nulla per valori negativi. Questo permette di poter definire sia l'iteratore di RPP sia quello di Mathos. *)

(* Nota: Quando si applica ad esempio una RPP di arietà 5 ad una lista, se ha lunghezza maggiore semplicemente verranno usati solo i primi 5 elementi e gli altri resteranno invariati (e non utilizzati) (ciò è dimostrato nel lemma "longer"); se la lunghezza è minore di 5 succederanno cose strane. *)

Open Scope Z_scope.

Fixpoint evaluate f (l : list Z) : list Z :=
  match f with
  | Id n => l
  | Ne => match l with []=>[] | x::l' => -x::l' end
  | Su => match l with []=>[] | x::l' => x+1::l' end
  | Pr => match l with []=>[] | x::l' => x-1::l' end
  | Sw => match l with x::y::l' => y::x::l' | _=>l end
  | Co f g => (evaluate g) (evaluate f l)
  | Pa f g => let n := arity f in
    evaluate f (l^[0,n]) ++ evaluate g (l^[n,∞])
  | It f => match l with []=>[]
    | x::l' => x::iter (evaluate f) (Z.to_nat x) l' end
  | If f g h => match l with []=>[]
    | x::l' => match x with
      | Zpos _ => x::evaluate f l'
      | Z0 => x::evaluate g l'
      | Zneg _ => x::evaluate h l'
      end
    end
  end.

(* \laq « f » \raq *)
Notation "« f »" := (evaluate f).



(* /// Permutazioni in RPP /// *)

(* Differenza: gli indici partono da 0. *)

(* Nota: nell'uso di queste permutazioni sfrutto la reversibilità, "faccio cose e poi quando ho finito faccio l'inversa". *)

Open Scope nat.

Fixpoint call i :=
  match i with
  | O => Id 1
  | S j => Id j ‖ Sw ;; call j
  end.
Fixpoint call_list l :=
  match l with
  | [] => Id O
  | i::l => call i ;; call_list l
  end.
Fixpoint prepare l :=
  match l with
  | [] => []
  | i :: l' => i + length (filter (λ j, i <? j) l') :: prepare l'
  end.
Definition perm l := call_list (rev (prepare l)).

Notation "\ l \" := (perm l) (at level 50).



(* /// Una libreria di funzioni in RPP /// *)

(* Differenza: nell'articolo sovente le funzioni hanno come argomenti gli indici su cui agiscono; io ho preferito non avere indici, e muovere direttamente gli argomenti con le permutazioni (rimettendoli a posto dopo con l'inversa della permutazione applicata). *)

Open Scope nat.

Definition id := Id 1.

Definition inc := It Su.
Definition dec := inv inc.

Definition tr := It (Su;; inc).
Definition cp := inc ;; id ‖ (tr ;; dec) ;; dec ;;
  \[0;3;1]\ ;; inc ;; \[0;2;1]\.

(* Nota: la funzione ifzsw ("if zero swap") prende come argomenti 3 elementi [x; y; 0]. Se almeno uno tra x e y sono uguali a 0 allora scambia x e y. *)

Definition ifzsw :=
  id ‖ (If id Su id;; Sw);;
  If id Su id;; Sw;;
  If Sw id id;;
  inv (id ‖ (If id Su id;; Sw);;
  If id Su id;; Sw).

(* Nota: questa funzione esegue un "passo" lungo il percorso tracciato dal Cantor pairing.
La funzione infatti prende 3 elementi [y; x; 0] e ritorna (per x≥0 e y≥0) 3 elementi [Y; X; 0], dove cp X Y = (cp x y) + 1.
Per come è definito il Cantor pairing ciò avviene in questo modo:
Se y=0 vogliamo che X=0 e Y=x+1:
[0; x; 0]     // valori iniziali
[0; x+1; 0]   // id ‖ Su
[0; x+2; 0]   // If id Su id
[x+2; 0; 0]   // ifzsw
[x+1; 0; 0]   // Pr
Se y>0 vogliamo che X=x+1 e Y=y-1:
[y; x; 0]     // valori iniziali
[y; x+1; 0]   // id ‖ Su
[y; x+1; 0]   // If id Su id
[y; x+1; 0]   // ifzsw
[y-1; x+1; 0] // Pr *)

Definition cu_step := id ‖ Su ;; If id Su id ;; ifzsw ;; Pr.

(* Nota: cu è l'inversa del Cantor pairing; dati 4 elementi [n; 0; 0; 0], cu esegue n volte cu_step ottenendo [n; x; y; 0] dove cp x y = n:
[n; 0; 0; 0]   // valori iniziali
[n; y; x; 0]   // It cu_step
[n; x; y; 0]   // id ‖ Sw
È come se a partire da (0,0), iterando n volte cu_step si "seguisse" il percorso tracciato dal Cantor pairing arrivando infine a (x,y).
Notare come in cu_step l'ordine di x, y sono invertiti, perciò bisogna eseguire uno swap finale. *)

(* Differenza: questa definizione di cu è molto più semplice ed efficiente di quella descritta nell'articolo. *)

Definition cu := It cu_step ;; id ‖ Sw.

(* Differenza: per come sono state definite cp e cu, la funzione push richiede 2 ancille anzichè 8. *)

Definition push := cp ;; \[2;0;1]\ ;; inv cu.
Definition pop := inv push.



(* /// Definizioni di base di PRF /// *)

(* Nota: ogni definizione che concerne le PRF è in maiuscolo, per distinguerle dalle definizioni delle RPP. *)

Open Scope nat.

Inductive PRF :=
  | ZE (n : nat)
  | SU (i n : nat)
  | PR (i n : nat)
  | CO (F : PRF) (Gs : list PRF)
  | RE (F G : PRF).

(* Differenza: si possono comporre funzioni con arietà diverse; l'arietà della composizione è definita come il massimo dell'arietà delle funzioni composte. *)

Fixpoint ARITY (F : PRF) : nat :=
  match F with
  | ZE n | SU _ n | PR _ n => n
  | CO F Gs => list_max (map ARITY Gs)
  | RE F G => S (ARITY F)
  end.

(* Differenza: anche qui gli indici partono da 0. *)

(* Differenza: la definizione di ricorsione primitiva usa un ordine degli argomenti un po' diverso: se H = RE F G allora
H (O::l) = F l
H (S n::l) = G (H (n::l)) n l *)

(* Nota: la ricorsione primitiva non è definita affatto in modo ricorsivo, ma piuttosto con un'iterazione.
Si è reso necessario definirla in questo modo poichè altrimenti Coq non mi accettava la definizione, non capiva come la ricorsione terminasse.
La funzione che viene iterata ha come argomento e restituisce una tripletta p=(a,b,c) che in Coq si definisce con le coppie ((a,b),c), perciò per riferirmi ad esempio all'elemento b devo usare snd (fst p). *)

Fixpoint EVALUATE F (l : list nat) : nat :=
  match F with
  | ZE n => 0
  | SU i n => S (nth i l 0)
  | PR i n => nth i l 0
  | CO F Gs => EVALUATE F (map (λ G, EVALUATE G l) Gs)
  | RE F G => match l with []=>0
    | n::l' => fst (fst (iter
      (λ p, (EVALUATE G (fst (fst p)::snd (fst p)::snd p), 1+snd (fst p), snd p))
      n
      (EVALUATE F l', 0, l') ))
    end
  end.

(* Nota: in teoria le PRF si possono combinare a piacimento, ma nella pratica affinché la funzione che verrà definita convert : PRF → RPP funzioni correttamente è necessario che le PRF siano "ben formate". Ciò viene formalizzato dalla proprietà induttiva strict.
Ad esempio per SU i n è necessario che i<n.
Quando si ha CO F Gs (quindi F(G1, G2, ...)) è necessario che
- F sia ben formata
- ogni G in Gs sia ben formata
- l'arietà di F sia uguale al numero di G (ovvero la lunghezza di Gs)
- l'arietà di tutte le G in Gs sia la stessa. *)

Inductive strict : PRF → Prop :=
  | strZE n :
      strict (ZE n)
  | strSU i n :
      i < n →
      strict (SU i n)
  | strPR i n :
      i < n →
      strict (PR i n)
  | strCO F Gs :
      strict F →
      Forall (λ G, strict G) Gs →
      length Gs = ARITY F →
      Forall (λ G, ARITY G = ARITY (CO F Gs)) Gs →
      strict (CO F Gs)
  | strRE F G :
      strict F →
      strict G →
      ARITY G = 2 + ARITY F →
      strict (RE F G).

(* Nota: le seguenti definizioni sono la versione "convertita" di SU e PR. *)

(* Nota: Mettere "Id (1+n)" è un modo semplice per fare in modo che la funzione abbia arietà almeno 1+n, il che è importante nella definizione di convert. *)

Definition conv_su i n :=
  Id (1+n) ;; Su ;; \[S i; 0]\ ;; inc ;; inv(\[S i; 0]\).

Definition conv_pr i n :=
  Id (1+n) ;; \[S i; 0]\ ;; inc ;; inv(\[S i; 0]\).

(* Nota: co_loading serve nella definizione di convert (CO F Gs).
Viene posta
n = arietà delle G in Gs (sotto ipotesi di strict (CO F Gs) ogni G in Gs ha la stessa arietà)
gs = [g1; ...; gm] = [convert G1; ...; convert Gm] = map convert Gs.
L'argomento di co_loading si può immaginare come l ++ 0' dove
l è una lista di lunghezza n, mentre 0' è una lista con un numero imprecisato di ancille (poste tutte a 0).
Ponendo ai = Gi L per i=1,...,m si ha
l ++ 0'                   // valori iniziali
[0] ++ l ++ 0'            // \[n]\
[a1] ++ l ++ 0'           // g1
[a1; a2] ++ l ++ 0'       // iterazione successiva
[a1; ...; am] ++ l ++ 0'  // dopo m iterazioni.

Per calcolare convert (CO F Gs) si procede in questo modo:
x :: l ++ 0'                                    // valori iniziali
x :: [a1; ...; am] ++ l ++ 0'                   // id ‖ co_loading n gs
l ++ x :: [a1; ...; am] ++ 0'                   // \seq (1+m) n\ = \[1+m;2+m;...;n+m]\
l ++ (x + F [a1; ...; am]) :: [a1;...;am] ++ 0' // Id n ‖ (convert F)
(x + F [a1; ...; am]) :: l ++ 0'                // applicando le inverse. *)

Fixpoint co_loading n gs :=
  match gs with
  | [] => Id 0
  | g::gs' => \[n]\ ;; g ;; id ‖ co_loading n gs'
  end.

(* Nota: re_forward serve nella definizione di convert (RE F G).
Si pone
n = arietà di F
f = convert F
g = convert G
L'argomento della funzione è dato da m :: l ++ 0' dove m è un numero naturale, l una lista di lunghezza n e 0' un numero imprecisato di ancille.
Se poniamo bi = (RE F G) (i::l) con i=0,...,m si ha
m :: l ++ 0'                          // valori iniziali
m :: [0; 0; 0; 0; 0; 0] ++ l ++ 0'    // id ‖ \seq n 6\ = id ‖ \[n;1+n;...;5+n]\
m :: [0; 0; 0; 0; 0; b0] ++ l ++ 0'   // Id 6 ‖ f
m :: [0; 0; 0; 0; b0 ;0] ++ l ++ 0'   // Id 5 ‖ Sw
Viene poi eseguita per m iterazioni la funzione
Id 3 ‖ (g ;; Sw) ;; \[0;3]\ ;; push ;; Id 5 ‖ Su
(con d, d', D si indicano generici numeri il cui valore preciso non ci interessa):
[0; 0; 0; 0; b0; 0] ++ l ++ 0'    // inizio prima iterazione
[0; 0; 0; b1; b0; 0] ++ l ++ 0'   // Id 3 ‖ g
[0; 0; 0; b0; b1; 0] ++ l ++ 0'   // Id 3 ‖ Sw
[0; b0; 0; 0; b1; 0] ++ l ++ 0'   // \[0;3]\
[d; 0; 0; 0; b1; 0] ++ l ++ 0'    // push
[d; 0; 0; 0; b1; 1] ++ l ++ 0'    // Id 5 ‖ Su
[d'; 0; 0; 0; b2; 2] ++ l ++ 0'   // dopo la seconda iterazione
[D; 0; 0; 0; bm; m] ++ l ++ 0'    // dopo l'm-esima iterazione
Con questo si conclude la definizione di re_forward.

Per calcolare convert (RE F G) si procede in questo modo:
x :: m :: l ++ 0'                       // valori iniziali
[x; m; D; 0; 0; 0; bm; m] ++ l ++ 0'    // id ‖ re_forward n f g
[bm; x; m; D; 0; 0; 0; m] ++ l ++ 0'    // \[6;0]\
[bm; x+bm; m; D; 0; 0; 0; m] ++ l ++ 0' // inc
x+bm :: m :: l ++ 0'                    // applicando le inverse. *)

Definition re_forward n f g :=
    id ‖ \seq n 6\ ;;
    Id 6 ‖ f ;;
    Id 5 ‖ Sw ;;
    It (Id 3 ‖ g ;; Id 3 ‖ Sw ;; \[0;3]\ ;; push ;; Id 5 ‖ Su).

Fixpoint convert (F : PRF) : RPP :=
  match F with
  | ZE n => Id (1+n)
  | SU i n => conv_su i n
  | PR i n => conv_pr i n
  | CO F Gs => let (n, m) := (ARITY (CO F Gs), length Gs) in

    id ‖ co_loading n (map convert Gs) ;; \seq (1+m) n\ ;;
    Id n ‖ (convert F) ;;
    inv (id ‖ co_loading n (map convert Gs) ;; \seq (1+m) n\)

  | RE F G =>
    id ‖ re_forward (ARITY F) (convert F) (convert G) ;;
    \[6;0]\ ;; inc ;; inv (\[6;0]\) ;;
    id ‖ inv (re_forward (ARITY F) (convert F) (convert G))
  end.

(* Nota: potrei sbilanciarmi e fare un'ipotesi di ottimalità sul numero di ancille molto debole: se nella definizione di convert F è permessa solo una ricorsione "semplice" (quindi per esempio dev'essere sempre possibile calcolare convert (RE F G) SOLO a partire da convert F e convert G, e quindi non sono ammesse ottimizzazioni furbe se si hanno da calcolare termini composti a più livelli come ad esempio convert (RE (RE F G) (RE A B))) allora la mia definizione di convert, con degli aggiustamenti, usa il minor numero di ancille possibile. Non insisterei su questo punto. *)

Definition anc F := arity (convert F) - (1+ARITY F).

(* Nota: la freccia all'insù è il casting da nat a Z, quella all'ingiù da Z a nat.
Due freccie all'insù sono il casting da list nat a list Z. *)

(* \upa ↑ *)
Notation "↑ n" := (Z.of_nat n) (at level 20).
Notation "↑↑ l" := (map Z.of_nat l) (at level 20).
(* \dow ↓ *)
Notation "↓ n" := (Z.to_nat n) (at level 20).

(* Nota: l'obiettivo principale della tesi è verificare
∀ F l x, thesis F l x
ovvero che per ogni F in PRF "ben formata" e con arietà uguale alla lunghezza di l vale che applicare "convert F" a x::l (con il casting e un numero di ancille appropriato) è come fare (x + F l) :: l. *)

Open Scope Z.

Definition thesis (F : PRF) (l : list nat) (x : Z) :=
  strict F →
  ARITY F = length l →
  «convert F» (x :: ↑↑l ++ repeat 0 (anc F)) =
  x + ↑(EVALUATE F l) :: ↑↑l ++ repeat 0 (anc F).