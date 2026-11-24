import YM.FormalOPE.RG10.Wing.Radii
/-! # Passage actual primitive Ward budget at zoom i, hierarchical. No claimed binding
 W or Gauge Δ action at held coarse fields. Producers supply jurisdictions. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Dispatch
open Function PowerSeries Finset Route HStein Submarine Patrol GaugeGear Tier
open scoped Topology BigOperators Classical
variable {X I B J: Type} (T:Tape X) (u:I→X)(v:B→X)
local notation "W"=>Channel (I⊕B)
local notation "m"=> Sum.elim u v
local notation "Δ"=>T.Δ
variable [Fintype I] [DecidableEq I] [Fintype B] [Fintype J]
variable (V:Episode I B J)(p:I⊕B→Channel (I⊕B))
local notation "A0"=> GaugeGear.first V
variable {k l d :ℕ} (F:Tier) {M C:ℝ}
-- explicit leading repeated rewrite prior to any curvature transform

def swing (V:Episode I B J)(p:I⊕B→Channel (I⊕B))(a:I): Packet (I⊕B):= GaugeGear.first V a + MvPolynomial.aeval (fun i=> PowerSeries.coeff 0 (craft V.spur i)) (PowerSeries.coeff 0 (p (Sum.inl a)))

structure Activate (V: Episode I B J)(p:I⊕B→ Channel (I⊕B)) (k d:ℕ)(u:I→X)(v:B→X) (T:Tape X)(F:Tier)(M C:ℝ) : Prop where
 stock : Inventory V F u v T M k d
 toll : Roads.Along T (Sum.elim u v) (Sum.elim u v) F k p M
 width : ∀ i,Guard (p i) k 1
 nilpot : steadyDown p
 first : ∀ a,(swing V p a).IsHomogeneous 1
 faith (a:I) : F.valueOf (fun b=> T.Δ (u a) (v b)) (GaugeGear.landing (swing V p a)) ≤ C
 nn : 0 ≤ C
-- replaces Books walt entire hypothesis

variable {T u v V p F}
local notation "λx"=> alternate V.spur p k
local notation "ℓ"=> orient V (alternate V.spur p k)
variable (Xc: Activate V p k d u v T F M C)
include Xc
private lemma gear0 (a:I): GaugeGear.first ℓ a = swing V p a:= by
 -- born lemma uses Episode with I+B both output approximated; can derive coeff_0 via replot compos.V.Need pure Mv lemma
 let R i:= coeff 0 (craft V.spur i)
 have he (q:Packet (I⊕B)): coeff 0 (MvPolynomial.aeval (craft V.spur) q)=MvPolynomial.aeval R q:= by
     induction q using MvPolynomial.induction_on with
     | C c=> rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]; rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,coeff_smul,coeff_zero_one]
     | add p q hp hq=> rw [map_add,map_add,map_add,hp,hq]
     | mul_X p i hp=> rw [_root_.map_mul, coeff_mul, MvPolynomial.aeval_X, _root_.map_mul,MvPolynomial.aeval_X,Finset.Nat.antidiagonal_zero, sum_singleton]; change coeff 0 _ * coeff 0 _ = _; rw [hp]
 change coeff 0 (replot _ _)= _; rw [replot_coeff, Finset.Nat.antidiagonal_zero, sum_singleton]; change coeff 0 (MvPolynomial.aeval _ (coeff 0 (lane p k _)))= _
 rw [Submarine.first p Xc.width Xc.nilpot,he,map_add, MvPolynomial.aeval_X]; rfl

private lemma marks (O:Lens T): Pre ℓ (O.m ∘ u) (O.m ∘ v) F C:= by
 let f t:= PowerSeries.C (stamp ℓ t); have hk : Roads.Along T u v F 0 f C:= fun a=> by
     unfold f; rw [Tier.gain_constant,stamp,gear0 Xc]; exact Xc.faith a
 refine ⟨fun i=> gear0 Xc i ▸ Xc.first i, fun i=>?_,fun i=>?_, Xc.nn⟩
 · have he:= Roads.rich T u v F 0 f C hk O i; unfold f at he; rwa [Tier.gain_constant] at he
 have he:=Roads.rich T u v free 0 f C (Roads.cashfree T u v F _ _ C hk) O i; unfold f at he; simpa only [Tier.gain_constant,free_stamp,one_mul] using he

-- budget for All branches grown by one polynomial for structural charge. No weighting P's assumed post.
def expand (k:ℕ):= total k + 2*(1+3*k)
local notation "P0"=> expand k
omit Xc in
lemma exponent (k):1 ≤ expand k:= by unfold expand total;omega

private lemma alongC : Roads.Along T m m F k (craft V.spur) M := by
 intro x; cases x with
 | inl a=> exact Xc.stock.ready a
 | inr a=>
   rw [show craft V.spur (Sum.inr a)=sprout _ from rfl,recital F _ (Sum.inr a) (fun _=> T.sign ..), T.paid,F.blind]; exact le_trans (by norm_num) Xc.stock.nn
private lemma alternate_across : Roads.Along T u m F k (alternate V.spur p k) (M^expand k) := by
 intro i; let O : Lens T:= ⟨fun a=> Δ (u i) a,fun _=> T.sign ..,fun a b=> T.train ..⟩; let m' := O.m ∘ m;
 have hz:0≤m':=fun a=> O.sign _; have hx := Xc.stock.nn; have hc : 0 ≤ M:= by linarith
 have he := changes m' hz (Roads.rich T _ _ _ _ _ _ Xc.toll O) (Roads.rich T _ _ _ _ _ _ (Roads.cashfree T _ _ _ _ _ _ Xc.toll) O) Xc.width hx Xc.stock.mind (Sum.inl i)
 have hw : F.gain m' (lane p k (.inl i)) k ≤ M^total k:= he.trans (le_of_eq (by rw [show m' (Sum.inl i)=0 from T.paid (u i),F.blind,mul_one]))
 apply le_trans (thoughts hz hz (Roads.rich T _ _ _ _ _ _ (alongC Xc) O) (Roads.rich T _ _ _ _ _ _ (Roads.cashfree T _ _ _ _ _ _ (alongC Xc)) O) hc _ (Guard.slim (Submarine.stays p Xc.width (Sum.inl i))) (by linarith)); unfold expand; rw [pow_add M (total k), mul_comm (M^total k), pow_mul M 2 (1+3*k)]; exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by nlinarith) _) hw (F.collect _ hz _) (by positivity)
private lemma cargo : Inventory ℓ F u v T (M^expand k) k d:= by
 have hx : M ≤ M^P0:= by have he:=pow_le_pow_right₀ (a:=M) (le_trans (by norm_num) Xc.stock.nn) (exponent k); simpa using he -- arg x inspect
 have hf := Xc.stock.law
 refine ⟨⟨fun i=> (hf.cov i).trans hx,fun ht i=> (hf.add ht i).trans hx⟩,⟨Xc.stock.le.rank,fun i=>?_⟩,alternate_across Xc,Xc.stock.nn.trans hx,Xc.stock.mind.trans hx,Xc.stock.cog.trans hx⟩
 apply Guard.prep (T:=craft V.spur) (Submarine.stays p Xc.width (Sum.inl i)); intro i; cases i with
 | inl i=> exact Xc.stock.le.spur _
 | inr i=> exact allowed (Sum.inr i)

lemma home (O:Lens T) (G: Subring (Channel I)) (he:∀ P∈G,Guard P k d→ Through k (kick p (replot (mark (B:=B)) P)) 0):
    Inventory ℓ F u v T (M^ expand k) k d ∧ Pre ℓ (O.m ∘ u) (O.m ∘ v) F C ∧ ∀ P∈G, Guard P k d→ pass V (alternate V.spur p k) P k:=
  ⟨cargo Xc,marks Xc O,fun P h J'=> Submarine.passenger P V.spur p Xc.width Xc.nilpot (he P h J')⟩ -- inspect order
end YM.FormalOPE.RG10.Wing.Dispatch
