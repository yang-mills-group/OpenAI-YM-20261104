import YM.MergeProof.North.Cent
import YM.Contact.Arose
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
open Relay Exponential Extraction Bid PhysicalNext.Repeat.Legato.Bandage
variable {G:Gauge}(C:Family G)(N p J k j m D d w:ℕ)(h:ℤ) {r:ℕ→ℕ} {W:Bid.Worth} {u ψ φ δ:ℕ→ℝ} {μ:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H"=> C.path
local notation "P"=> C.path.levels.budget
local notation "Y"=> C.path.levels
local notation "V"=> Site (C.side J p)
local notation "rad"=> radiusJ C m
variable (x:Cover)(B: C.label d) (T:C.label w) (hf:J ≤ k) (hk:k ≤ m) (hm:m+1 < j) (F:Extraction.Order)
local notation "f"=> (fun (x:Cover) (N p:ℕ)=> chip C N p j m D d w h B T x)
variable (hh:C.Makes)(hR:Created C)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r μ)
variable {i₀:ℕ}{σ χ:ℕ→ℝ}
variable (b a e X η c:ℝ)
local notation "A"=> twoStakes C j m d w h b a
variable (hB:(C.labels.level d).coeffSize B ≤ a) (hT:(C.labels.level w).coeffSize T ≤ b)
local notation "W'"=> holder C.path.levels j m δ φ η A
local notation "P'"=> (C.path.levels.budget (m+1))
local notation "B!"=> ((P').B^2+1+2*blast C.path.levels m)
structure RichNode (ε:ℝ) : Prop where
    corners : ∀ x:Cover, rad/16≤ ‖C.S.gridPoint j x‖→ ‖C.S.gridPoint j x‖≤4*(ranula C.path.levels m) → ∃ z:ℕ×ℕ→ C.label D,∃ A' :ℝ, F.late fun N p=> ∃ hJ: J≤N, ‖z (N,p)‖≤ A' ∧ Interior ((center C.S p hJ 0).chamber 0) (f x N p (z (N,p)))∧ (center C.S p hJ 0).rootTest (C.beta N p) (f x N p (z (N,p))) ≤ ε
local notation "L'"=> C.S.a J
-- L.lower arbitrary.X
include hh hp hR hB hT hm hf hk
lemma toggled (ha:0<a)(hb:0<b)(hw:0<c)(r₀:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 J k)(hK:C.ref D ≤ k)(h':C.ref d ≤ j)(hT':C.ref w ≤ j)(hW:32*(ranula C.path.levels m) ≤ L')
   (Y' H':ℕ→ℝ)(hr:Wares C (δ:=δ) (r:=r) (μ:=μ) i₀ D χ Y' H')(hI:i₀ ≤ m)(HE:X=H' m)(HB:η=Y' (m+1)) (hR':GridApprox.room C.path.levels J m (lensScope C D))
   (hΩ:C.S.a (m+1) * B! ≤ C.S.a J)(hL:march (fun _:Unit=>c) φ k m () ≤ δ m * (W'/(16*X)))
   (hV:0 < W')(hA:4*(1+(C.path.levels.params m).columns)*(2*(C.S.a (m+1)^D*(X*(4*(1/W')))))≤ e)
   (hC:32*(1+(C.path.levels.params m).columns)*c * ‖alto C.path k D‖*(e/gainChart C.path m k) ≤ fly C.path.levels D k/2) :
   RichNode C J -- edit params auto order check
     j m D d w h B T F (2*(stakes C J k/c)):= by
   constructor; intro x hq hhq
   have hY:= hf.trans (hk.trans m.le_succ)
   obtain ⟨Q,hP,hQ⟩:= Next.UVStress.quota_stop C hh (hK.trans hk)
   let Qtt:= Q*(2*e); let A':=2*(stakes C J k /c)
   have hw':∀ᶠ i:ℕ×ℕ in F.fuse,∃ (ht:J ≤ i.fst) (v:C.label D),‖v‖≤ Qtt∧ Interior ((center C.S i.2 ht 0).chamber 0) (f x i.1 i.2 v)∧ (center C.S i.2 ht 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v)≤A':=by
       rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually (faraway C j x)] with p hp'
       filter_upwards [F.mesh.cofinal.eventually (eventually_gt_atTop j),F.mesh.cofinal.eventually (near_center C J d hh), F.mesh.cofinal.eventually (near_center C J D hh), F.mesh.cofinal.eventually (near_center C J w hh)] with N hj hs hS ht
       let n:=F.mesh N; let q:=F.per p; have hh':J≤n:= by change j<n at hj; omega
       change ∃ (hx:J ≤ n) (v:C.label D), _; refine ⟨hh',?_⟩
       let ℓ:= wrap (C.side j q) x; have hp0 : C.S.place ℓ= C.S.gridPoint j x:=hp'; let Z:= center C.S q hh' 0
       have hq' : 8* ‖C.S.place (0:Site (C.side n q))‖ ≤ C.S.a J:=by rw [latzero]; simp [(C.S.a_pos J).le]
       have hl : Interior (Z.chamber 0) (C.O n q T (Cells.location C.S j n q x)):=by
          apply ht hh'; have hN:j ≤ n:= (show j < n from hj).le; rw [Cells.location,dif_pos hN, C.S.embeds_place (C.S.toDepth hN q),hp']; linarith only [hhq,hW]
       have hΩ' : (((Y|>.budget (m+1)).B)^2+1+2*blast C.path.levels m) ≤ (C.S.toDepth hY q).count.val:=by
          exact_mod_cast (le_of_mul_le_mul_left (hΩ.trans_eq (C.S.embeds_scale (C.S.toDepth hY q)).symm) (C.S.a_pos _))
       let scale' := max (rad) (‖C.S.place ℓ‖/4); have hrLow: rad ≤ scale':=le_max_left ..; have hρ : scale'/16≤ ‖C.S.place ℓ‖∧ ‖C.S.place ℓ‖ ≤ 4*scale' :=by
            dsimp only [scale']; rw [hp0]; rcases max_choice (radiusJ C m) (‖C.S.gridPoint j x‖/4) with Hq|Hq <;> rw [Hq] 
            · exact ⟨hq,by linarith only [le_of_eq Hq,le_max_right (radiusJ C m) (‖C.S.gridPoint j x‖/4)]⟩
            have hn:=norm_nonneg (C.S.gridPoint j x); exact ⟨by linarith,by ring_nf; rfl⟩
       obtain ⟨v,hq,H',hx⟩:= wallSupply C n q J k j m D d w h x B T hf hk hm hj hh hR hp b a e X η c hB hT scale' hrLow (max_le (faster ..) (by rw [hp0]; linarith only [hhq])) ha hb hw r₀ hx hK h' hT' hρ.1 hρ.2 hl (hs hh' q _ hq' B) (fun v=>hS hh' q _ hq' v) Y' H' hr hI HE HB hR' hΩ' hL hV hA hC
       refine ⟨v,(hQ n q v ?_).trans (mul_le_mul_of_nonneg_left hq hP),H',hx⟩; change j < n at hj;omega
   let pred (i:ℕ×ℕ)(v:C.label D):Prop:=∃ hV:J ≤ i.1, ‖v‖≤ Qtt ∧ Interior ((center C.S i.2 hV 0).chamber 0) (f x i.1 i.2 v) ∧ (center C.S i.2 hV 0).rootTest (C.beta i.1 i.2) (f x i.1 i.2 v) ≤ A'
   have he : ∀ᶠ i:ℕ×ℕ in F.fuse, ∃ v,pred i v:=hw'.mono fun i h=> by obtain ⟨hi,v,h,r⟩:=h; exact ⟨v,hi,h,r⟩
   let z(i:ℕ×ℕ): C.label D:=if h:∃ v,pred i v then h.choose else 0
   refine ⟨z,Qtt,?_⟩; change ∀ᶠ i:ℕ×ℕ in F.fuse, pred i (z i); exact he.mono fun i h=>by unfold z;rw [dif_pos h];exact h.choose_spec
end
end YM.MergeProof.Ribbons
