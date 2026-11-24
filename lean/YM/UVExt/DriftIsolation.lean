import YM.UVExt.TwoTone

/-! Relative one-loop scalar coefficient check using *all* periods of the same kernel and same sheet.

Does not control the remaining nonlinear reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Precision RG Lattice Wilson Matrix Laurent Tree Exterior Bid Tensor Set Function Next.Free
open scoped ContDiff Topology BigOperators Classical
variable {G : Gauge} {A : Levels G} {P : MapPrices} {M : Horizon A} {s : Supply.Sheet G} {N:Supply.Rolls s} {Q : PostCost N} {H : ChartRatio G} (K : Kin M H)
    (h : Discipline P A M) (hk : K.Planned Q) (u : ℕ→ℕ) (hu : Tendsto u atTop atTop) (v : ℕ→ℕ) (hv : Tendsto v atTop atTop)
    {U V : ℕ→Shadow G} (hU : ∀ m, woodPassing K u m U) (hV : ∀ m,woodPassing K v m V)
    {X : (i:ℕ)→Transfers A i} (hX : Follows A u M X)
    {x y : ℕ→ℝ} (hp : ∀ i,Tendsto (fun j=>K.alpha (u j) i) atTop (𝓝 (x i))) (hp' : ∀ i,Tendsto (fun j=>K.alpha (v j) i) atTop (𝓝 (y i))) (hN : LocalRatio H)
    (hh : ∀ d,confluent K u v 4 d)

noncomputable def ruby {u v} {U V} (hU : ∀ m,woodPassing K u m U) (hV : ∀ m,woodPassing K v m V) (x y : ℝ) m p (z : Dir G (A.S.side m p)) := x* (Tensor.diagonal ((hU m).economicTensor (A.S.side m p) 2) z) - y* (Tensor.diagonal ((hV m).economicTensor (A.S.side m p) 2) z)
noncomputable def loopDrift {u v} {U V} (hU : ∀ m,woodPassing K u m U) (hV : ∀ m,woodPassing K v m V) {m p : ℕ} (z : Dir G (A.S.side m p)) := discrep ((hU m).spiralTensor (A.S.side m p) 2) ((hV m).spiralTensor (A.S.side m p) 2) z
noncomputable def inflation (Q : PostCost N) (i) := Q.Γ (A.clock.J (i+1))* loopprice G (jrate A i) 1 -- etc
noncomputable def dust {G : Gauge} {A : Levels G} {s : Supply.Sheet G} {N:Supply.Rolls s} (Q : PostCost N) (m p) := tolerance (A.S.side m p) (Q.Γ (A.clock.J (m+1))) (Q.c (A.clock.J (m+1))) (A.clock.loopCap (m+1))

include h hk hu hv hU hV hX hN hp hp' hh
lemma drift_eq (i p : ℕ) (l l' : Site (A.S.side i p)) (σ τ : TypeFace 1 → G.ColorIndex → ℂ) (he : ∀ a t, ‖σ a t‖ ≤ 1) (hτ : ∀ a t,‖τ a t‖≤1) :
    let w := wave (G:=G) l σ + wave l' τ
    |ruby K hU hV (x i) (y i) i p w + loopDrift K (m:=i) hU hV (p:=p) w - loopDrift K (m:=i+1) (p:=p) hU hV (mapBind A M X i p w)| ≤ 8*dust (A:=A) Q i p := by
       intro w
       let S := A.clock.op i p
       let F : Forest S.ratio := Classical.choice (select S.ratio S.patch.odd_side); let r : S.Choices := Classical.arbitrary _
       have hP := proc K hk i u hu p F r; have hQ := proc K hk i v hv p F r
       have hS := Thermal.mk (L:=hP) (hu.eventually (eventually_gt_atTop i) |>.mono fun j hj=> hk.retains (u j) i p hj F); have hT := Thermal.mk (L:=hQ) (hv.eventually (eventually_gt_atTop i) |>.mono fun j hj=>hk.retains (v j) i p hj F) -- explicit L?
       exact true_wave_bill hP hQ hN (fun j=>K.alpha (u j) i) (hU (i+1)) (hU i) (hV (i+1)) (hV i) hS hT ((hh p) _) (hX.installs i p) (Q.price _) (Q.price _) l l' σ τ he hτ (hp i) (hp' i)

omit h hk hu hv hX hN hp hp' hh
lemma coin_upper (m p) (z : Dir G (A.S.side m p)) :
    |loopDrift K (m:=m) (p:=p) hU hV z| ≤ 2*((Fintype.card (Site (A.S.side m p)):ℝ)*loopprice G (jrate A m) (jlambda A m) * gradD z * ‖dColor G _ 1 z‖) := by
   have hs := twin_near z (hU m); have hh := twin_near z (hV m)
   unfold loopDrift discrep; simp_rw [(hU m).loopLimit _ 2 |>.2, (hV m).loopLimit _ 2 |>.2]
   exact (_root_.abs_sub ..).trans (by linarith [hs.2,hh.2]) -- defin
end YM.UVExt.Paths
