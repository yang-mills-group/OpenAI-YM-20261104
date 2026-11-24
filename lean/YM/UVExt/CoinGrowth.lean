import YM.UVExt.DriftIsolation

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Precision RG Lattice Wilson Matrix Laurent Tree Exterior Bid Tensor Set Function Next.Free
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {A : Levels G} {P : MapPrices} {M : Horizon A} {s : Supply.Sheet G} {N:Supply.Rolls s} {Q : PostCost N} {H : ChartRatio G} (K : Kin M H)
    (h : Discipline P A M) (hk : K.Planned Q) (u : ℕ→ℕ) (hu : Tendsto u atTop atTop) (v : ℕ→ℕ) (hv : Tendsto v atTop atTop)
    {U V : ℕ→Shadow G} (hU : ∀ m, woodPassing K u m U) (hV : ∀ m,woodPassing K v m V)
    {X : (i:ℕ)→Transfers A i} (hX : Follows A u M X)

def shelter (A : Levels G) (i) := loopprice G (jrate A i) (jlambda A i)
def qual (A : Levels G) (P : MapPrices) (m i : ℕ) := towerPrice A.clock.kernel.penalty P (A.clock.J (m+1)) (A.clock.J m) / (A.S.block m).val^i
lemma omega_pos (A : Levels G) {M : Horizon A} (P : MapPrices) (h : Discipline P A M) (j : ℕ) : 0 ≤ P.Ω (A.clock.J j) := by
    obtain ⟨hh,hi,hi'⟩ := ((h.plan.rows j j le_rfl).2.2.2.1 (plaquette (show PlaqAxes from ⟨(0,1),by decide⟩)) (plaquette (show PlaqAxes from ⟨(0,1),by decide⟩)))
    exact (tsum_nonneg hh).trans hi'
lemma qual_pos (A : Levels G) (P : MapPrices) {M : Horizon A} (h : Discipline P A M) (m i) : 0≤ qual A P m i := by
  apply div_nonneg ?_ (by positivity)
  apply le_trans ?_ ((basic_fees (i:=A.clock.J (m+1)) (j:=A.clock.J m) (P:=P) (A.clock.kernel.penalty) (omega_pos A P h _) (omega_pos A P h _)).1)
  exact mul_nonneg (Nat.cast_nonneg _) (omega_pos A P h _)
include K hX h hu
private lemma frame_prices (m p : ℕ) (z : ℂ) (a : G.Color) (hp : ‖a‖=1) (hz : ‖z‖≤1) (hc : 4 ≤(A.S.side m p).val) :
    let w := melody a (A.S.side m p) z
    let f:= mapBind A M X m p w; let ε := ripple (n:=A.S.side m p)
    ‖dColor G _ 1 w‖ ≤ 4*ε ∧ gradD w ≤4*ε^2 ∧ ‖dColor G _ 1 f‖ ≤ (qual A P m 2)*4*ε ∧ gradD f ≤ (qual A P m 3)*4*ε^2 := by
    intro w f ε
    unfold qual; obtain ⟨_,hx,hd⟩ := Follows.bottom A M P hu h hX m p w
    obtain ⟨hQ,h'⟩:= cochain_tone a hp hc z hz
    exact ⟨hQ,h',hx.trans ((mul_le_mul_of_nonneg_left hQ (qual_pos A P h m 2)).trans_eq (by unfold qual; ring)), hd.trans ((mul_le_mul_of_nonneg_left h' (qual_pos A P h m 3)).trans_eq (by unfold qual; ring))⟩ -- if cast equality. add hu to include
omit K hX h hu in
lemma shelter_pos (A : Levels G) i : 0≤shelter A i := by unfold shelter jrate jlambda RG.Calendar.loopCap loopprice; positivity [show 0≤ Real.exp (1:ℝ) by positivity, show 0≤A.clock.monitor i ^ A.clock.theta (A.clock.J i) by exact Real.rpow_nonneg (by unfold Calendar.monitor; positivity) _, (A.params i).width_pos.le]

def postal (A : Levels G) (P : MapPrices) m :=
   2*(2*shelter A m *16 * (4*Real.pi)^3 + 2*((A.S.block m).val:ℝ)^4*shelter A (m+1) * (qual A P m 3) * (qual A P m 2) *16*(4*Real.pi)^3)

include hV hu hU
set_option maxHeartbeats 500000 in
lemma stripe_fee (m p : ℕ) (a b : ℝ) (z : ℂ) (w : G.Color) (hw : ‖w‖=1) (hz : ‖z‖≤1) (hf : 4≤(A.S.side m p).val)
          (hd : let w' := melody w (A.S.side m p) z
   |ruby K hU hV a b m p w' + loopDrift K (m:=m) (p:=p) hU hV w' - loopDrift K (m:=m+1) (p:=p) hU hV (mapBind A M X m p w')| ≤ 8*dust (A:=A) Q m p)
 : |ruby K hU hV a b m p (melody w (A.S.side m p) z)| ≤ (postal A P m)/2*(A.S.side m p).val + 8*dust (A:=A) Q m p := by
 let n := A.S.side m p; let t : ℝ := n.val
 let a' := A.S.side m p; let r := ruby K hU hV a b m p; let Δ {i} := loopDrift K (m:=i) (p:=p) hU hV; let N := mapBind A M X m p
 let w' := melody w (A.S.side m p) z; let L : ℝ := (A.S.block m).val
 let C := shelter A m; let B := shelter A (m+1); let U := qual A P m 2; let V := qual A P m 3; let d := dust (A:=A) Q m p
 change |r w'| ≤ 2*(2*C * 16 * (4*Real.pi)^3 + 2*L^4*B * V * U *16*(4*Real.pi)^3)/2*t+8*d -- check postal order
 let f:=N w'
 obtain ⟨h₁,h₂,h₃,h₄⟩ := frame_prices K h u hu hX m p z w hw hz hf
 have hC := shelter_pos A m; have hB := shelter_pos A (m+1); have hU1 := qual_pos A P h m 2; have hV1 := qual_pos A P h m 3
 have ht : 0 < t := Nat.cast_pos.mpr n.property
 have hN : (Fintype.card (YM.Lattice.Site (A.S.side (m+1) p)):ℝ)=(t*L)^4 := by
    unfold Schedule.side YM.Schedule.denominator t n L; rw [Lattice.site_card,Nat.cast_pow,Schedule.side]; simp only [PNat.mul_coe,Nat.cast_mul]; ring
 let ε := ripple (n:=n); let D:=dColor G n 1; let D':= dColor G (A.S.side (m+1) p) 1
 have hε : ε = (4*Real.pi)/t := rfl
 have hi₁ := coin_upper K u v (hU:=hU) (hV:=hV) m p w'; have hi₂ := coin_upper K u v (hU:=hU) (hV:=hV) (m+1) p (N w')
 rw [show (Fintype.card (Lattice.Site n):ℝ)=t^4 from by unfold t; rw [YM.Lattice.site_card]; norm_num] at hi₁
 rw [hN] at hi₂
 have hi₀ : 0 ≤ ε := ripple_pos n|>.le
 have hi₁ := hi₁.trans <| calc
    _ ≤  (2:ℝ)*(t^4*C*(4*ε^2)*(4*ε)) := mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left h₂ (by dsimp [C]; positivity)) h₁ (norm_nonneg _) (by positivity)) (by norm_num)
    _ = (2:ℝ)*C*16*(4*Real.pi)^3*t := by rw [hε]; field_simp; ring
 have hi₂ := hi₂.trans <| calc
    _ ≤ (2:ℝ)*((t*L)^4*B*(V*4*ε^2)*(U*4*ε)) := by
       apply mul_le_mul_of_nonneg_left _ (by norm_num : 0≤(2:ℝ)); exact mul_le_mul (mul_le_mul_of_nonneg_left h₄ (show 0≤(t*L)^4*B from by positivity)) h₃ (norm_nonneg _) (by positivity)
    _ = 2*L^4*B*V*U*16*(4*Real.pi)^3*t := by rw [hε]; field_simp; ring
 change |r w' + Δ w' - Δ f| ≤ 8*d at hd
 have hT : (2:ℝ)*(2*C*16*(4*Real.pi)^3+2*L^4*B*V*U*16*(4*Real.pi)^3) / 2 * t+8*d= 8*d+2*C*16*(4*Real.pi)^3*t+2*L^4*B*V*U*16*(4*Real.pi)^3*t := by ring
 rw [hT, show r w' = (r w'+Δ w'-Δ f) - Δ w' + Δ f from by ring] -- rw will rewrite occurrences occurrences? 
 exact (abs_add_le ..).trans (add_le_add ((abs_sub ..).trans (add_le_add hd hi₁)) hi₂)
end YM.UVExt.Paths
