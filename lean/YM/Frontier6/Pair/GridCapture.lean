import YM.MergeProof.North.Brim
import YM.Frontier6.Pair.FusionCost

/-!
# Full-annular pair capture on the actual extraction grid.

Follows the Brim proof of ShellNode, changing the range of configurations,
costs and fields. Output placed at left input at cutoff; continuum centroid
output later obtained by derivative system. `Quota` retained (cannot blindly
convert to power counting by grading).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid
variable {G:Gauge} (C:Family G) (N p J k j m d d' D:ℕ)
variable {r:ℕ→ℕ}{W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}
variable {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "R"=>C.path.levels
local notation "ν"=>renal C.path.levels
local notation "B'"=>fuga C.path.levels m
local notation "Z"=>fusionSpan C.path.levels m
variable (x:Cover) (B:C.label d) (T:C.label d')
variable (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (F:Extraction.Order)

def pairFragment (N p:ℕ) (z:C.label D): Config G (C.side N p) → ℂ:=
   C.O N p B 0 * C.O N p T (Cells.location C.S j N p x) - C.O N p z 0

local notation "f"=> (fun (x:Cover) (N p:ℕ)=> pairFragment C j d d' D x B T N p)

structure ShellPairs (budget ε:ℝ) : Prop where
    corners : ∀ x:Cover, fuga C.path.levels (m+1)/16 ≤ ‖C.S.gridPoint j x‖→ ‖C.S.gridPoint j x‖ ≤ 4*B' →
       ∃ z:Rowe C D, ∀ᶠ i : ℕ × ℕ in F.fuse, ∃ hJ:J ≤ i.1,
        m ≤ i.1 ∧ Next.UVStress.quota C D m i.1 i.2 (z i) ≤ budget ∧
        Interior ((center C.S i.2 hJ 0).chamber 0) (f x i.1 i.2 (z i))∧
        (center C.S i.2 hJ 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 (z i)) ≤ ε

variable (hM:C.Makes)(hR:Created C)(hp:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r μ)
variable (b a w:ℝ)
variable (hV:Velour C (renal C.path.levels) r μ)
local notation "P"=> (C.path.levels.budget (m+1))
local notation "A!"=> partnerRates C j d d' b a
local notation "V!"=> pairLaunch C j m d d' b a
local notation "e!"=> pairQuota C j m d d' D b a
local notation "X!"=> bling R m
local notation "B!"=> ((P).B^2+1+2*Z)
include hV hM hp hR hf hk hm

set_option maxRecDepth 2048 in
lemma offsetMatch (hb:0<b)(ha:0<a)(hw:0<w)(hB:(C.labels.level d).coeffSize B ≤ b)(hT:(C.labels.level d').coeffSize T ≤ a)
   (r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(h':C.ref d ≤ j)(hT':C.ref d' ≤ j)(hW:32*B' ≤ C.S.a J)
   (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ:C.S.a (m+1) * B! ≤ C.S.a J)(hL:march (fun _:Unit=>w) (near C.path.levels) k m () ≤ ν m * (V!/(16*X!)))
   (hY:0 < V!)
   (hC:32*(1+(C.path.levels.params m).columns)*w * ‖alto C.path k D‖*(e!/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   ShellPairs C J j m d d' D B T F (2*e!) (2*(stakes C J k/w)):= by
   constructor; intro x hq hhq
   obtain ⟨χ,hχ⟩:= hV.mother; obtain ⟨σ,hσ⟩:=(hχ D).city
   have hI:=hK.trans hk; have hΔ:= hI.trans m.le_succ; have hy:= hf.trans (hk.trans m.le_succ)
   let A':=2*(stakes C J k /w)
   let pred (i:ℕ×ℕ)(v:C.label D):Prop:=∃ hJ:J ≤ i.1, m ≤ i.1 ∧ Next.UVStress.quota C D m i.1 i.2 v ≤ 2*e! ∧ Interior ((center C.S i.2 hJ 0).chamber 0) (f x i.1 i.2 v) ∧ (center C.S i.2 hJ 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v) ≤ A'
   have he : ∀ᶠ i:ℕ×ℕ in F.fuse, ∃ v,pred i v:=by
       rw [Extraction.Order.fused,Extraction.Order.late]
       filter_upwards [F.per.cofinal.eventually (faraway C j x)] with p hp'
       filter_upwards [F.mesh.cofinal.eventually (eventually_gt_atTop j),F.mesh.cofinal.eventually (near_center C J d hM), F.mesh.cofinal.eventually (near_center C J D hM), F.mesh.cofinal.eventually (near_center C J d' hM)] with N hj hs hS ht
       let n:=F.mesh N; let q:=F.per p; change j<n at hj; have hh':J≤n:= by omega
       let J':=center C.S q hh' 0; let ℓ:=wrap (C.side j q) x
       have hp0 : C.S.place ℓ= C.S.gridPoint j x:=hp'
       have hl : Interior (J'.chamber 0) (C.O n q T (Cells.location C.S j n q x)):=by
          apply ht hh'; rw [Cells.location,dif_pos hj.le, C.S.embeds_place (C.S.toDepth hj.le q)]; change 8* ‖C.S.place ℓ‖ ≤ _; rw [hp0]; linarith only [hhq,hW]
       have hh : 8* ‖C.S.place (0:Site (C.side n q))‖ ≤ C.S.a J:=by rw [latzero]; simp [(C.S.a_pos J).le]
       have hs:= hs hh' q _ hh B
       have hΩ' : B! ≤ (C.S.toDepth hy q).count.val:=by
          exact_mod_cast (le_of_mul_le_mul_left (hΩ.trans_eq (C.S.embeds_scale (C.S.toDepth hy q)).symm) (C.S.a_pos _))
       let t:Bool→ℕ:= Bool.rec d d'; let t':Π i:Bool,C.label (t i):= Bool.rec (motive:=fun i=> C.label (t i)) B T
       let s:Bool→ Config G (C.side n q)→ℂ:= Bool.rec (C.O n q B 0) (C.O n q T (Cells.location C.S j n q x))
       have hX (i:Bool): s i = C.O n q (t' i) (bites C J j q ℓ n (0,i)):= by
          cases i
          · rw [biteF,zeroMama C J q n hh'];
          rw [biteT C J j q n ℓ hh', vect C _ q n ℓ hj.le, show (C.S.toDepth hj.le q).embed ℓ= Cells.location C.S j n q x from by rw [Cells.location,dif_pos hj.le]]
          -- refl
       have hv(i:Bool): A! i * Spindle.paid C (t i) j n q (t' i) ≤ fly C.path.levels (t i) j :=by
          cases i
          · exact paid_new C n q j d hM B b hb hB h' hj
          exact paid_new C n q j d' hM T a ha hT hT' hj
       have hA(i:Bool):0 < A! i:= by cases i; exacts [stockpit C j d b hb,stockpit C j d' a ha]
       have hi(i:Bool): Interior (J'.chamber 0) (s i):=by cases i; exacts [hs,hl]
       have h₀:= (span_used C.path.levels m); obtain ⟨hh₁,hh₂⟩:= longMaximizing C j q (m+1) ℓ hm.le (by rw [hp0]; exact hq) (by rw [hp0]; exact le_trans (add_le_add_left hhq _) h₀) -- add-le
       have hy : ∀ z:C.label D, Interior (J'.chamber 0) (C.O n q z 0) := fun v=> hS hh' q _ hh v
       obtain ⟨z,hZ,hE⟩:= longMutation C n m q D J k w (A!) ℓ hf hk hj hm t t' hM hp hI hR r₀ hx hK (Bool.rec (motive:=fun i=> C.ref (t i) ≤ j) h' hT') hv hA hR' hΩ' hh₁ hh₂ s (fun i=>by rw [hX i]; exact (itemT C n q _ hM (t' i) _).symm) (fun i=> by rw [hX i]; exact C.continuousO ..) hi hy hσ ((hχ D).funs _ hΔ|>.1) ((hχ D).funs _ hΔ|>.2) ((hχ D).brings m hI n q _|>.2) ((hχ D).dollars m hI) ((hχ D).crisp j (by omega)) (fun i he hp0=> (hχ D).brings i (by omega) n q (hp0.trans hj)|>.1) ((hχ D).bars _ hΔ|>.1) ((hχ D).bars _ hΔ|>.2) hw hL hY (le_refl (e!)) hC
       exact ⟨z, hh',show m ≤ n by omega,hZ, Next.UVStress.minus ((hi false).times (hi true)) (hy _),hE⟩
   let z(i:ℕ×ℕ): C.label D:=if h:∃ v,pred i v then h.choose else 0
   refine ⟨z,?_⟩; change ∀ᶠ i:ℕ×ℕ in F.fuse, pred i (z i); exact he.mono fun i h=>by unfold z;rw [dif_pos h];exact h.choose_spec

omit hf hk hm
lemma captures_all (hG:G.Simple) (r₀:Stock.Tabs C.path.levels)(hb:0<b)(ha:0<a)(hB:(C.labels.level d).coeffSize B ≤ b)(hT:(C.labels.level d').coeffSize T ≤ a) (hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)
   {j:ℕ→ℕ}{t y:ℝ}(hT' : Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t))(hj:Tendsto j atTop atTop)(ht:∀ᶠ i in atTop,i+1<j i)(hY:y+(((d:ℝ)+(d':ℝ))*t+8*(t-1)) < (1/8)+(d:ℝ)+(d':ℝ)) :
   ∀ᶠ m in atTop, ShellPairs C J (j m) m d d' D B T F (2*pairQuota C (j m) m d d' D b a) (2*(stakes C J k / exteriorReserve C m d d' D y)):=by
   filter_upwards [offset_price C hG hT' hj r₀ hb ha hp y k hK hY,hj.eventually_ge_atTop (C.ref d),hj.eventually_ge_atTop (C.ref d'),offset_lightness C hG hV J, ht,eventually_ge_atTop k,Push.GridApprox.plenty C.path.levels J (lensScope C D)] with m ⟨⟨he,hL⟩,hϑ⟩ h h' ⟨hr,hR'⟩ hm hN hJ
   exact offsetMatch C J k (j m) m d d' D B T hx.1 hN hm F hM hR hp b a (exteriorReserve C m d d' D y) hV hb ha (Real.exp_pos _) hB hT r₀ hx hK h h' hr hJ (by push_cast at hR'; exact hR') hL he hϑ
end
end YM.MergeProof.Ribbons
