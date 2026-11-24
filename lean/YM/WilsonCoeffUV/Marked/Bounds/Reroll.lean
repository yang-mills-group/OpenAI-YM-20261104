import YM.WilsonCoeffUV.Marked.Bounds.ClozeTag
/-!
# Native root-interval reindexing (ink AND full product)

An `Outerm` array need only be lazy outside each queried subset. Inputs can be
zero outside any assignments/ideals. Each output coefficient log dependent
only on that root assignment/relabeling preimages and on subassignments &
incoming vacuum branch. Full product law preserved even if inputs are mixed
logs, providing exact normalization conversion.
 -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Metric Shard Realm PathCost
open scoped Topology BigOperators
variable {c f:Side}{ι α U β V t:Type}{J K I S T:Finset ι}{p:ι→U}{d:Bank.Distance U}{D k:ι→ℕ}{i j i' j' a e r h N n m l:ℕ}{G:Gauge}{σ τ u A B C:ℝ}
variable [DecidableEq ι]

lemma levels_g {P Q:family G D}{S}(h:∀ J⊆ S,P J=Q J): levelsO P S=levelsO Q S:=by
    induction S using Finset.strongInduction with
    | H t ih=>
        rw [levelsO,levelsO]; split; · rfl
        congr 1; apply Finset.sum_congr rfl; intro i _; split
        next x=> rw [h _ x.1, ih _ (sh_k x.1 x.2) (fun _ u=> h _ (u.trans Finset.sdiff_subset))]
        rfl
lemma reverse_g {P Q:family G D}{S}(h:∀ J⊆S,P J=Q J): reverseO P S=reverseO Q S:=by
    induction S using Finset.strongInduction with
    | H t ih=> rw [reverseO,reverseO]; split; · rfl
               rw [h _ le_rfl]; congr 2; apply Finset.sum_congr rfl; intro i _; split
               next x=> rw [h _ Finset.sdiff_subset, ih _ (lt_of_le_of_ne x.1 x.2) (fun _ u=> h _ (u.trans x.1))]
               rfl
lemma levels_S_eq {P Q:family G D}{A:Levels G}{Ñ:ChartRatio G}{S}(h:∀ J⊆ S,P J=Q J): edV A Ñ m N P k S= edV A Ñ m N Q k S:=by unfold edV; rw [levels_g h]
lemma log_g {P Q:family G D}{A:Levels G}{Ñ:ChartRatio G}{S}(h:∀ J⊆ S,P J=Q J): logO A Ñ m N P k S=logO A Ñ m N Q k S:= reverse_g (fun _ p=>levels_S_eq (fun i hi=> h i (hi.trans p)))

abbrev Outerm (G:Gauge)(D:ι→ℕ) := (ι→Cover)→ family G D
def Solo (k:ι→ℕ)(P:Outerm G D): Prop:=∀ p,Eu k (P p)
def lazy (P:Outerm G D):Prop:=∀ p q S,(∀ i∈ S,p i=q i) → P p S=P q S
def muting (P:Outerm G D): Prop:=∀ p,P p ∅=0
abbrev backRow (c:Side)(S:Finset ι):= S→Site c
variable (P:Patch)
def inflate (S:Finset ι)(X:backRow P.L S):ι → Site P.L:=fun i=> if h:i∈ S then X ⟨i,h⟩ else 0
def copyQ (p:ι→Cover)(w:ι→Site P.L) : ι→Cover:=fun i=> P.L.val • p i+lift (w i)
def splitQ (p:ι→ Cover)(S:Finset ι)(w:backRow P.L S) : ι→Cover := copyQ P p (inflate P S w)
-- projection solely by root cover-ancestry, old external stencil moved by folio
abbrev scalesK (K:ι→ℕ)(J:Finset ι) := ∏ j∈J,(P.L.val:ℝ)^K j/ (P.L.val:ℝ)^4

lemma scalesSplit (K:ι→ℕ)(h:J⊆S): scalesK P K S=scalesK P K J * scalesK P K (S\J):=by rw [mul_comm]; exact (Finset.prod_sdiff h).symm
omit [DecidableEq ι] in
lemma scalesBound (K:ι→ℕ)(J:Finset ι): 0≤ scalesK P K J:= Finset.prod_nonneg fun _ _=> by positivity

def portV (K:ι→ℕ)(X:Outerm G D)(p:ι→ Cover)(S:Finset ι)(j:backRow P.L S) : Era G (Pen D S):=scalesK P K S • tuftV (mend P (inflate P S j) D S) (X (splitQ P p S j) S)
def unite (K:ι→ℕ)(X:Outerm G D)(p:ι→Cover) (S: Finset ι): Era G (Pen D S):=∑ j:backRow P.L S, portV P K X p S j
lemma road (K:ι→ℕ)(X: Outerm G D)(p:Solo k X)(v S w) : Auth (mass k S) (portV P K X v S w):= ((p _ _).tuft _).μ _
lemma cone_L (K:ι→ℕ)(X:Outerm G D)(p:Solo k X): Solo k (unite P K X):= fun v S=>Auth.sum fun _ _=> road P K X p v S _
lemma wield (K:ι→ℕ)(X:Outerm G D)(v:lazy X): lazy (unite P K X):=by
   intro p q S z; apply Finset.sum_congr rfl; intro i x; rw [portV,portV,v _ (splitQ P q S i) _ (fun i' h=>by unfold splitQ copyQ; rw [z i' h])]
lemma tuftZero [NormedAddCommGroup U][NormedSpace ℝ U][NormedAddCommGroup V][NormedSpace ℝ V](f: U→L[ℝ]V): tuftV f (0: Era G U)=0:= Prod.ext (funext fun _=>map_zero _) (map_zero _)
lemma upQuiet (K:ι→ℕ)(X: Outerm G D)(x:∀ p,X p ∅=0) : ∀ p, unite P K X p ∅=0:=by intro p; apply Finset.sum_eq_zero; intro i _; rw [portV,x,tuftZero,smul_zero]
omit [DecidableEq ι] in
lemma brand {D:ι→ℕ}(p q:ι→Site P.L)(A:Case D)(u:∀ i∈ J,p i=q i): seaMark (laid P p A) J= seaMark (laid P q A) J:= by
    apply Subtype.ext; ext x; change folio _ _ _= folio _ _ _; apply Finset.prod_congr rfl; intro i hi; unfold laid; rw [u i hi]
omit [DecidableEq ι] in
lemma buckHit (V:Case D)(F: Era G (Pen D S))(p:ι→Site P.L): readO V (tuftV (mend P p D S) F) c=readO (laid P p V) F c:=by
    apply congr_arg flash; funext i j x; exact mend_v ..

def streak (K:ι→ℕ) (X:Outerm G D)(n:Side)(p:ι→Cover)(A:Case D)(S:Finset ι)(v:backRow P.L S): Ink (Woods G n) := scalesK P K S • readO (laid P (inflate P S v) A) (X (splitQ P p S v) S) n
lemma stare (K:ι→ℕ)(X:Outerm G D)(h:Solo k X)(v n p A): readO A (portV P K X p S v) n= streak P K X n p A S v:=by unfold streak portV; rw [read_rho _ _ _ ((h _ _).tuft (mend P (inflate P S v) D S)),buckHit]
lemma stalwart (K:ι→ℕ)(X: Outerm G D)(h:Solo k X)(n p A) : readO A (unite P K X p S) n=∑ j:backRow P.L S,streak P K X n p A S j:=by
    rw [unite, read_Sum A n (fun i _=> road P K X h p S i)]; exact Finset.sum_congr rfl fun i _=>stare P K X h i n p A
omit [DecidableEq ι] in
lemma brandS {D:ι→ℕ}(p q:ι→Site P.L)(V: Case D)(n:Side)(X: Era G (Pen D S))(h:∀ i∈S,p i=q i) : readO (laid P p V) X n=readO (laid P q V) X n:=by
   apply congr_arg flash; funext i j z
   exact congr_arg (X.1 n i j z) (brand P p q V h)

def lowerV (P: Patch)(h:J⊆ S)(v:backRow P.L S): backRow P.L J:= fun i=>v ⟨i.val,h i.property⟩
lemma lowTrail (h:J⊆S)(v:backRow P.L S)(X:Outerm G D)(x:lazy X)(p V n):
   readO (laid P (inflate P S v) V) (X (splitQ P p S v) J) n=readO (laid P (inflate P J (lowerV P h v)) V) (X (splitQ P p J (lowerV P h v)) J) n:=by
    have hp i (e:i∈J): inflate P S v i=inflate P J (lowerV P h v) i:=by unfold inflate; rw [dif_pos (h e),dif_pos e]; rfl
    rw [x (splitQ P p S v) (splitQ P p J _) _ (fun i z=> by unfold splitQ copyQ; rw [hp i z])]; exact brandS P _ _ _ _ _ hp
lemma eCurse {D K:ι→ℕ}{M L:Outerm G D}(p:Solo k M)(q:Solo k L)(v:lazy M)(b:lazy L) (u:∀ p A (n:Side), Equation (feeble (M p) A n) (feeble (L p) A n))(A:Case D)(n:Side)(x:ι→Cover): Equation (feeble (unite P K M x) A n) (feeble (unite P K L x) A n):=by
   let m S:= ∑ j:backRow P.L S,streak P K M n x A S j; let l S:= ∑ j:backRow P.L S,streak P K L n x A S j
   rw [show feeble _ A n=m from funext fun S=> stalwart _ _ _ p n x A, show feeble _ A n=l from funext fun S=>stalwart _ _ _ q n x A]
   have hu P A:= u P A n; refine ⟨?_,?_,?_⟩
   · unfold m; rw [Fintype.sum_unique]; unfold streak; rw [show readO _ (M _ ∅) n=1 from (hu _ _).1]; simp [scalesK]
   · unfold l; rw [Fintype.sum_unique]; unfold streak; rw [show readO _ (L _ ∅) n=0 from (hu _ _).2.1]; exact smul_zero _
   -- convolution by reindex Fintype decomposition
   funext S; unfold dial m shells; rw [Finset.smul_sum]; let u S':=streak P K M n x A S'; let L' S':=streak P K L n x A S'; let χ (y:backRow P.L S) S':= readO (laid P (inflate P S y) A) (L (splitQ P x S y) S') n; let μ (y:backRow P.L S) S':=readO (laid P (inflate P S y) A) (M (splitQ P x S y) S') n
   have he i:S.card • u S i=∑ j∈S.powerset,scalesK P K S • (j.card • χ i j * μ i (S\j)) :=by
       have hv: S.card • μ i S= ∑ j∈ S.powerset,j.card • χ i j * μ i (S\j):= congr_fun (hu _ _).2.2 S; change S.card • (scalesK P K S • μ i S)=_; rw [← Finset.smul_sum, ←hv, smul_comm]
   change ∑ i,S.card • u S i= _; simp_rw [he]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; have hf:= Finset.mem_powerset.mp hi; have hz:S\i⊆ S:=Finset.sdiff_subset
   let J:= backRow P.L i; let T:=backRow P.L (S\i); let W:= backRow P.L S
   let F (j:W) : J×T:= (lowerV P hf j,lowerV P hz j); let B:= Equiv.ofBijective F (show Bijective F from ?_)
   · have hp : i.card • l i= ∑ j:J,i.card • L' i j:= by unfold l; rw [Finset.smul_sum]
     rw [hp,Finset.sum_mul]; simp_rw [Finset.mul_sum]; rw [←Fintype.sum_prod_type']; refine Fintype.sum_equiv B _ _ (fun j=>?_)
     rw [scalesSplit P K hf]; let a:= B j
     have h0: χ j i=readO (laid P (inflate P i a.1) A) (L (splitQ P x i a.1) i) n:= lowTrail P hf j L b x A n; have h1: μ j (S\i)=readO (laid P (inflate P (S\i) a.2) A) (M (splitQ P x (S\i) a.2) (S\i)) n:=lowTrail P hz j M v x A n
     rw [h0,h1]; change _= i.card • (_ • _) * (_ • _); rw [smul_comm (i.card),mul_smul, smul_mul_assoc, mul_smul_comm,smul_comm (scalesK P K i) (scalesK P K (S\i)),smul_mul_assoc,smul_mul_assoc]
   constructor
   · intro a b e; funext j; by_cases h:j.val∈ i; · exact congr_fun (congr_arg Prod.fst e) (⟨j.val,h⟩: ↑i)
     exact congr_fun (congr_arg Prod.snd e) (⟨j.val,Finset.mem_sdiff.mpr ⟨j.property,h⟩⟩: ↑(S\i))
   intro j; let f (y:S):= if p:y.val∈i then j.1 ⟨y.val,p⟩ else j.2 ⟨y.val,Finset.mem_sdiff.mpr ⟨y.property,p⟩⟩; refine ⟨f,Prod.ext ?_ ?_⟩
   · funext s; exact dif_pos s.property
   funext s; exact dif_neg (Finset.mem_sdiff.mp s.property).2
end YM.WilsonCoeffUV.Wheel.Mark
