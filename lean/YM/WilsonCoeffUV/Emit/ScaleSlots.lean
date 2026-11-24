import YM.WilsonCoeffUV.RootLaw
import YM.WilsonCoeffUV.Stable.Analytic.Step
import YM.WilsonCoeffUV.Marked.Capture.Earned
/-!
# Slot scalar factors in mixed-address LOG and capture models

Keep polynomial-Λ costs out of the exp-window/gale exponent. Use even for impulses
with different coupling normalizations (after reexpression in common formal units).
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.ScaleS
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Flooring
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α U:Type}{J I S T:Finset ι}{D k K:ι→ℕ}{i j a e r h N m b b' l:ℕ}{G:Gauge}{σ B z ρ:ℝ}{E W V U':Credit}{A:Levels G}{Ñ:ChartRatio G}
variable [DecidableEq ι]
lemma waxRate (h:J ⊆ S)(X: Era G (Pen D J))(Y: Era G (Pen D (S\J)))(a:Auth i X)(b: Auth j Y)(c d:ℝ) : waxV h (c•X) (d•Y)=(c*d) • waxV h X Y:=by
    apply read_ext _ _ (paidW h _ _ (a.μ c) (b.μ d)) ((paidW h _ _ a b).μ _); intro F n
    rw [read_wax h F n _ _ (a.μ _) (b.μ _), read_rho F n _ a,read_rho F n _ b,read_rho F n _ (paidW h _ _ a b),read_wax h F n _ _ a b,mul_smul, smul_mul_assoc,mul_smul_comm]
lemma catchS (w:ι→ℝ)(h:J⊆ S): (∏ j∈J,w j)*(∏ j∈(S\J),w j)=∏ j∈ S,w j:=by rw [mul_comm,Finset.prod_sdiff h]
abbrev compound (w:ι→ℝ)(X:family G D) : family G D := fun i=> (∏ j∈i,w j) • X i
abbrev withinC (w:ι→ℝ)(X:Outerm G D) : Outerm G D := fun i=> compound w (X i)
lemma levelsFactor (h:family G D)(v:Eu k h)(w:ι→ℝ) (S:Finset ι): levelsO (compound w h) S=compound w (levelsO h) S:=by
    induction S using Finset.strongInduction with
    | H S ih=>
      change _= _ • levelsO h S
      conv_lhs => rw [levelsO]
      conv_rhs => arg 2; rw [levelsO]
      by_cases e:S=∅
      · subst S; rw [Finset.prod_empty,one_smul,dif_pos rfl,dif_pos rfl]
      rw [dif_neg e,dif_neg e,smul_comm (∏ i∈S,w i)]; apply congr_arg _; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; split
      next x=>
        rw [ih _ (sh_k x.1 x.2)]; dsimp only [compound]
        rw [waxRate x.1 _ _ (v _) (placedO _ v _),catchS w x.1,smul_comm (∏ i∈S,w i)]
      next x=> rw [smul_zero]
lemma reverseFactor (h:family G D)(v:Eu k h)(w:ι→ℝ)(S:Finset ι): reverseO (compound w h) S=compound w (reverseO h) S:=by
    induction S using Finset.strongInduction with
    | H S ih=>
      change _=_ • reverseO h S
      conv_lhs => rw [reverseO]
      conv_rhs => arg 2; rw [reverseO]
      by_cases e:S=∅
      · subst S; rw [Finset.prod_empty,one_smul]; rw [dif_pos rfl,dif_pos rfl]
      rw [dif_neg e,dif_neg e,smul_sub, smul_comm (∏ i∈S,w i)]; apply congr_arg₂ (·-·) rfl; apply congr_arg _; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; split
      next x=> rw [ih _ (lt_of_le_of_ne x.1 x.2)]; dsimp only [compound]; rw [waxRate x.1 _ _ (counted _ v _) (v _),catchS w x.1,smul_comm (∏ i∈S,w i)]
      next x=> rw [smul_zero]
omit [DecidableEq ι] in
lemma tuftR {V U: Type*}[NormedAddCommGroup U][NormedSpace ℝ U][NormedAddCommGroup V][NormedSpace ℝ V](X:Era G U)(T:U→L[ℝ]V)(x:ℝ): tuftV T (x • X)=x • tuftV T X:=by
   refine Prod.ext ?_ ?_; · exact funext fun n=> map_smul (ply T.toLinearMap) x (X.1 n)
   exact map_smul (ply T.toLinearMap) x X.2
lemma uniteFactor (P:Patch)(K:ι→ℕ)(w:ι→ℝ)(X: Outerm G D): unite P K (withinC w X)=withinC w (unite P K X):=by
   funext p S
   rw [withinC,compound,unite,unite,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=>by unfold portV withinC compound; rw [tuftR,smul_comm]
lemma edFactor {P:family G D} (p:Eu k P)(h:G.Simple)(v:LocalRatio Ñ)(f:m<N)(w:ι→ℝ): edV A Ñ m N (compound w P) k= compound w (edV A Ñ m N P k):=by
   funext S; rw [edV,levelsFactor P p w]; change verseI A Ñ m N (mass k S) ((∏ i∈S,w i) • levelsO P S)=_ • verseI A Ñ m N (mass k S) (levelsO P S); simpa only [Finset.sum_singleton] using verse_sum A h f v (S:={0}) (P:=fun _ : ℕ=> levelsO P S) (fun _ _=>placedO _ p S) (fun _=>∏ i∈S,w i)
lemma stoutFactor {P:Outerm G D}(p: Wellness k P)(h:G.Simple)(v:LocalRatio Ñ)(f:m<N)(w:ι→ℝ): stout A Ñ m N K k (withinC w P)=withinC w (stout A Ñ m N K k P):=by
   let L:=stout A Ñ m N K k P; let Q:=fun u=> logO A Ñ m N (P u) k; have he u: logO A Ñ m N (withinC w P u) k =withinC w Q u:=by
       unfold logO; change reverseO (edV A Ñ m N (compound _ _) k)=_; rw [edFactor (A:=A) (p.level' u) h v f]; exact funext fun S=>reverseFactor _ (vol A Ñ m N (P u) k f h v (p.level' u)) w S
   rw [stout,show (fun u=> logO A Ñ m N (withinC w P u) k)=withinC w Q from funext he,uniteFactor]
lemma gearsFactor (p:G.Simple)(x:LocalRatio Ñ)(w:ι→ℝ){X:Outerm G D}(h:Wellness k X)(q:b≤N)(v:m≤ b): Gears A Ñ K k N b m (withinC w X)=withinC w (Gears A Ñ K k N b m X):=by
    induction v using Nat.decreasingInduction with
    | self=> rw [gearTop,gearTop]
    | of_succ i a ih=> rw [gearUp _ _ _ a, gearUp _ _ _ a, ih, stoutFactor (Cog A Ñ (K':=K) q X h p x a) p x (a.trans_le q)]
lemma centralRate (S:SealR G)(U:Verse S.F)(x:ℝ) : centralL A Ñ N m b S (x • U)=x • centralL A Ñ N m b S U:=by
    unfold centralL polarP steep; rw [Matrix.mulVec_smul,show music _ (x • _)= x • music _ _ from ?_, StableStrip.shrine_μ]; funext i; rw [music, Pi.smul_apply, Pi.smul_apply,music]; exact map_smul (PowerSeries.substAlgHom _) x _
abbrev onSlots (Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F)(w:ι→ℝ):=fun s=> w s • (X s)
lemma coatFactor (Q:ι→SealR G)(X:(s:ι)→ Verse (Q s).F)(w:ι→ℝ) : coatA A Ñ N m Q (onSlots Q X w)=withinC w (coatA A Ñ N m Q X):=by
    funext p S; by_cases h:S.card=1
    · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp h; rw [coatLeaf,withinC,compound,Finset.prod_singleton,coatLeaf,onSlots,centralRate]; unfold cn; rw [tuftR]; rfl
    rw [coatLazy _ _ _ _ _ _ _ _ h,withinC,compound,coatLazy _ _ _ _ _ _ _ _ h,smul_zero]

end YM.WilsonCoeffUV.Wheel.ScaleS
