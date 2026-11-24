import YM.OPE.Compatible.Roan.Baste
/-! # checkpoints geometry. full inside Θ leases. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)(p:Site L.f) (Y:Studio L)(w: Bid.Dir G L.c)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
lemma Dtn_tag {n:Side}(x y z:Site n): Dtn x z≤ Dtn x y+Dtn y z:=by exact_mod_cast separation_triangle x y z
lemma DtCom {n:Side}(x y:Site n): Dtn x y=Dtn y x := congr_arg (fun i:ℕ=>(i:ℝ)) (separation_comm x y)
lemma DtHi {n:Side}(x y:Site n):0≤Dtn x y:=Nat.cast_nonneg _
structure ReserveQ (ℓ:ℝ):Prop where
        worth : ∀ i:Key Fθ G,Dtn p (pointK L.Z Fθ i) ≤ 64*ℓ →i.1∈ Y.X
        fits : ∀ i:Wings G L.c,Dtn p (cotW L.Z i) ≤ 64*ℓ → cash (JetB G L.c) Y.w i= cash (JetB G L.c) w i
abbrev Training (p:Site L.f)(X:Seats Fθ)(ℓ:ℝ):Prop:=∀ i:Key Fθ G,i.1∈ X→ Dtn p (pointK L.Z Fθ i)≤ ℓ
lemma hides (ht: ReserveQ L p Y w ℓ)(he:0 ≤ℓ)(i:Drive L)(hz:Dtn p (Wct L i)≤ 20*ℓ): Rebound L Y w ℓ i:=by
       rcases i with i|i
       · exact ht.fits i (hz.trans (by linarith))
       have he': i.1∈ Y.X:= ht.worth i (hz.trans (by linarith)); let j: Rubric G Y.X:= (⟨_,he'⟩,i.2); let c:=pointK L.Z Fθ i; have hp (v:Site L.f) (hv:¬ Dtn p v≤64*ℓ):ℓ ≤ Dtn c v:=by
            change Dtn p c ≤20*ℓ at hz; linarith only [hz,he,Dtn_tag p c v, not_le.mp hv]
       have hh : shout G Y.X j=i:= rfl; exact ⟨j,rfl,(fun k hv=>hp _ (fun he=>hv (ht.fits k he))),(fun k hv=> hp _ (fun he=>hv (ht.worth k he)))⟩
section
variable (J:Finset (Rubric G Y.X))
abbrev Lix (i:Rubric G Y.X):Drive L:= .inr (shout G Y.X i)
lemma Hired (X:Finset (Drive L))(hx:∀ i∈X,Dtn p (Wct L i)≤ t):∃ J:Finset (Rubric G Y.X), J.card ≤ X.card ∧ (∀ i∈J,Dtn p (Wct L (Lix L Y i))≤ t)∧ ∀ i∈X,Hst L Y J i:=by
       let f(p:Rubric G Y.X):= Lix L Y p; let J:=Finset.univ.filter fun i=> f i∈ X; have hg(i:Rubric G Y.X)(he:i∈J):= (mem_filter.mp he).2; refine ⟨J,le_trans ?_ (card_le_card (s:=J.image f) (t:=X) (fun i hi=>?_)),fun i hi=>hx (f i) (hg _ hi),fun i hi=>?_⟩
       · rw [Finset.card_image_of_injective _]; intro i j h; exact (shout G Y.X).injective (Sum.inr.inj h)
       · obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact hg _ hj
       rcases i with i|i; · trivial
       intro h; exact mem_filter.mpr ⟨Finset.mem_univ _,hi⟩ -- hi f ...
lemma Alien (k:Drive L)(hz: t+u≤ Dtn p (Wct L k))(h:∀ i∈J,Dtn p (Wct L (Lix L Y i))≤ t): remote L Y J k u:=by
       intro i; have ht:= h i.val i.property; let c:= Wct L (Lix L Y i.val); let v:= Wct L k; change u≤ Dtn v c; have hh : Dtn p v≤ Dtn p c+Dtn v c:= (DtCom v c) ▸ (Dtn_tag p c v); linarith only [ht,hh,hz] -- linarith definitional
noncomputable def Voy (X:Seats Fθ): Finset (Drive L):= Finset.univ.image (fun i:Rubric G X=> Sum.inr (shout G X i): Rubric G X→ Drive L)
lemma joinsQ (X:Seats Fθ)(i:Key Fθ G)(h:i.1∈X):Sum.inr i∈ Voy L X:=mem_image.mpr ⟨(⟨_,h⟩,i.2),Finset.mem_univ _,rfl⟩
-- near root package
lemma auction (X:Seats Fθ)(hk:Training L p X t)(Q:Finset (Drive L))(he:∀ i∈Q,Dtn p (Wct L i)≤ t):∃ J:Finset (Rubric G Y.X), J.card ≤ X.card*Fintype.card G.ColorIndex+Q.card∧ (∀ i∈ J,Dtn p (Wct L (Lix L Y i))≤ t) ∧ (∀ i:Key Fθ G,i.1∈ X → Hst L Y J (Sum.inr i)) ∧ ∀ i∈Q,Hst L Y J i:=by
       let R:=Voy L X; have hx:R.card ≤ _:=Finset.card_image_le (s:=Finset.univ) (f:=fun i:Rubric G X=> Sum.inr (shout G X i))
       have ht:∀ i∈ R ∪ Q,Dtn p (Wct L i) ≤ t:=by
            intro i hi; obtain h|h:=Finset.mem_union.mp hi; · obtain ⟨i,hi,rfl⟩:=mem_image.mp h; exact hk _ i.1.property
            exact he _ h
       obtain ⟨J,hP,hS,hq⟩:= Hired L p Y (R ∪ Q) ht; exact ⟨J,hP.trans ((Finset.card_union_le ..).trans (add_le_add (hx.trans_eq (by rw [card_univ,Fintype.card_prod,Fintype.card_coe])) le_rfl)),hS,fun i hi=> hq _ (Finset.mem_union_left _ (joinsQ L X i hi)),fun i hi=>hq _ (Finset.mem_union_right _ hi)⟩
end
end
end YM.OPE.Borealis.Galea
