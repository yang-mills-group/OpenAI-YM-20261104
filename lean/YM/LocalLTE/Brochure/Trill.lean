import YM.LocalLTE.Brochure.Ring
/-! # Visit booking. Analytic proposal challenge. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals Progress.DirectedRecipe
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} {R: Roost.Factor A}{p0:ℕ} -- use eta
variable {ε : ℝ} (H:Funding R p0 ε) {p:ℕ} (W : Trail H p) (M:Preview H) (P0:Bolt A)
local notation "c"=>A.B.a
local notation "T"=> A.B.a.clock
local notation "P"=> P0.history
variable (ρ:ℕ)
namespace Coterie
open YM.LocalLTE YM.LocalLTE.Fan YM.LocalLTE.Port
local notation "xt" m=> A.B.a.clock.hatBeta (m)
local notation "L" m=>D.L (A.B.a.clock.J (m+1))
local notation "Q" m=> betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))
variable {Mζ CB N m n u:ℕ} {r0:ℕ→ℕ→ℕ} {μ ζ σ:ℝ} {Wz:Wickets R.target p ζ}
variable {H W M P0 ρ}
variable (S:Circuit Mζ CB ρ p r0 H W M μ ζ σ Wz P0)
open Marker Overlay MergeProof.Menu
variable (N m n u)
variable (hm:m<N)(hv:u ≤ Mζ)
variable {V:Type}[DecidableEq V][Fintype V] (Qt:Marker.Census V)
set_option quotPrecheck false
local notation "s"=> (wgt A m μ u)
local notation "d"=> berry A m
local notation "v₁"=> (ung A (m+1))
local notation "v₀"=> (ung A m)
local notation "Pτ"=> (P N n (m+1))
local notation "Tτ"=> (P N n m)
local notation "Z"=> (Wz.tuner u)
local notation "Y'"=> (Q m)
local notation "z'"=> Y'^(-ζ)
local notation "E!"=> ((gStep (Pτ).beta)^(ρ+1:ℕ))
local notation "κℓ"=> H.κ
local notation "j'"=> A.B.a.clock.J (m+1)
local notation "i'"=> A.B.a.clock.J m
local notation "Z'"=> A.B.a.clock.op m n
local notation "c'"=> A.B.a.S.side m n
local notation "S'"=> (S.fortune N m n hm)
local notation "R1"=> (S').inletX
local notation "R0"=> (S').outletX
local notation "W" => A.B.a.params (m+1)
open Cadence
variable (U':Cadence Qt (P0.history N n (m+2)))(T1:Cadence Qt (P0.history N n (m+1))) (T0:Cadence Qt (P0.history N n m))
variable (hu0:Fintype.card V≤ CB)
local notation "β"=> (Q m)
local notation "Pt" => (X.p.profile j')
variable (hv':m+1<N)(a:ℝ) (ha:0 ≤ a) (hr:0<ζ)(ht:u< Mζ)
include S hv' hu0 ht hr ha
lemma stroll (hp:Forts (P0:=P0) (H:=H) N (m+1) n u (μ:=μ) (Wz:=Wz) Qt U' T1 a): let Y:=β; Opened N m n (u+1) (μ:=μ) (Wz:=Wz) (P0:=P0) (H:=H) Qt T1 a (books Y ζ) (books Y ζ) (past Y ζ) (past Y ζ) (past Y ζ):=by
     let m₁:=m+1; let j:=j'; let i:= i'; let k:= A.B.a.clock.J (m₁+1)
     have hw:= Peer.ge (H:=H) (m:=m)
     have hβ:=beta_eq A.B.valid m; have he:= step_paid (A.B.a) m; have he' := step_paid (A.B.a) m₁
     have hB:0<β:=zero_lt_one.trans_le hw
     let y:=β; let z:= Q m₁
     let t:= ballast y
     let W'(_:V):= wgt A (m+1) μ u; let W₁(_:V):= wgt A m μ (u+1)
     have ht₀:0 ≤ t:= Real.rpow_nonneg hB.le _; have ht₁: t≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos hw (by norm_num)
     have he₀ : y ≤ z:=by unfold y; rw [← hβ]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
     have hk:= S.forecast.wake _ _ he _ (A.B.valid.pays m)
     have hk₀:= S.forecast.wake _ _ he' _ (A.B.valid.pays m₁)
     have hV (v:V): W₁ v ≤ t* W' v := by unfold W' W₁ wgt t y; rw [← hβ]; exact hk₀.2.2 u ht
     have hK (v:V):0 < W₁ v:= Real.rpow_pos_of_pos hB _
     have hf:(Pτ).p=A.B.a.budget (m+1):= (Peer.faith (S.fortune N m n (by omega))) -- syntax
     have hg:T1.sure.Radial W₁ a (books y ζ) (past y ζ) v₁∧ T1.plan.Radial W₁ a (books y ζ) (past y ζ) v₁∧ T1.extra.Radial W₁ 0 (past y ζ) (past y ζ) v₁:=by -- v1 next inlet divisor.P
        let e:=y^(-ζ); let e':=z^(-ζ); let v0:= v₁; let b:=books y ζ; let c0:=past y ζ
        have hb:= Port.centralBank _ _ hp.spent _ hK ht₀ ht₁ hV
        have hv:= Port.centralBank _ _ hp.proj _ hK ht₀ ht₁ hV
        have hC:= Port.centralBank _ _ hp.error _ hK ht₀ ht₁ hV
        rw [mul_zero] at hC hv
        have ha₀:t*a≤a:=mul_le_of_le_one_left ha ht₁
        have he:e'≤e:= Real.rpow_le_rpow_of_nonpos hB he₀ (neg_nonpos.mpr hr.le)
        have he₁:t*e'≤ c0:= mul_le_mul_of_nonneg_left he ht₀
        have hc₀ : z^aust ≤ y^aust:= Real.rpow_le_rpow_of_nonpos hB he₀ (by norm_num [aust]); have hee:0 ≤ e:=Real.rpow_nonneg hB.le _
        have hb' : t*(z^aust+e')≤ b:= mul_le_mul_of_nonneg_left (add_le_add hc₀ (show e'≤e from Real.rpow_le_rpow_of_nonpos hB he₀ (neg_nonpos.mpr hr.le))) ht₀
        have hw':t* z^aust≤ b:= mul_le_mul_of_nonneg_left (hc₀.trans (le_add_of_nonneg_right hee)) ht₀
        have hv':0 ≤ ung A (m+1):= Real.sqrt_nonneg _
        refine ⟨Port.budgetUp _ _ hb ha₀ hw' (mul_le_mul_of_nonneg_right he₁ hv'),Port.budgetUp _ _ hv ha₀ hb' (mul_le_mul_of_nonneg_right (mul_nonneg ht₀ hee) hv'), Port.budgetUp _ _ hC le_rfl he₁ (mul_le_mul_of_nonneg_right he₁ hv')⟩
     refine ⟨⟨hp.boots,hg.1,hp.projected,hg.2.1,hp.delta,hg.2.2,hp.tabs⟩,?_, ?_⟩
     · apply hp.angel _ (S.signs.stalk.pinch u ht j i k he' he); unfold berry; let b:= (Z).bbase k j
       rw [hβ]; have hh : radiusB y ≤ 2 * radiusB (A.B.a.clock.hatBeta m):=hk.2.1; have hvh: 2*b≤ (D.L j).val:= S.signs.stalk.side k j u ht he'; refine le_trans (Nat.mul_le_mul_left b hh) ?_; rw [← Nat.mul_assoc, Nat.mul_comm b]; exact Nat.mul_le_mul_right _ hvh
     have hV' : v₁=Urns.divisor β:=by unfold ung; change Real.sqrt (Real.exp (- ((A.B.a.clock.monitor (m+1))^(1/5:ℝ)))) = _; unfold Calendar.monitor; rw [hβ]; rfl
     have hw:= params_eq A.B.valid (m+1); let B:= (Pτ).p
     have hB : B.power=(Pt).power ∧ B.order=(Pt).order:=by unfold B; rw [hf]; exact ⟨congr_arg Stage.power hw,congr_arg Stage.order hw⟩
     change capacity (Pτ).p V _ _ v₁ _ _ _≤ _; rw [hV']; exact hk.1.serve V hu0 (Pτ).p hB.1 hB.2
end Coterie
end YM.PhysicalNext.Repeat.Mallow
