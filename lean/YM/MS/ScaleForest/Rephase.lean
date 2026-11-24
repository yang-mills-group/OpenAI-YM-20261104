import YM.MS.ScaleForest.Ordered
import YM.MS.Fiddle.Born
/-!
# Multi-source use of the SAME dimensional angular continuation

Between-pin branches will have *another* integrated momentum, even when the
joining edge is a bridge. Anchors lie in the preferred four dimensions and
for this different kind of gluing we put an entire phase on one side,
including on the joining line's momentum. Assemble the requisite covariant (`Sturdy` false,
i.e. rotations fixing the four dimensions) products. Off all
contact strata, phase factors buy arbitrary powers of the small length in
that momentum integral itself. Later need this estimate before the limit in z;
begin by proving the algebra of rephasings and prices at a point.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Fiddle
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {s : ℂ} {R : Set ℂ} {U : Rip G} {a b δ : I → ℝ} {X Y : Mob G} {f g : I → Mob G} {A : QP} {P : I→QP} {m n : ℕ} {K : LineRule G}

def weave (X Y : Mob G) : Mob G := fun n=> product (field Landau.parity) (X n) (Y n)

abbrev onPlane (m : ℕ) : SectorP m→L[ℝ] QP := Cl (Nat.zero_le m)
abbrev waveFact (A : QP) (p : SectorP m) : ℂ := Tone.bill A (onPlane m p)

def rephase (A : QP) : (Mob G) →ₗ[ℂ] (Mob G) where
   toFun X := fun _ l=> waveFact A (net l)*X _ l
   map_add' _ _:= funext fun _=> funext fun _=> mul_add ..
   map_smul' _ _:= funext fun _=> funext fun _=> mul_left_comm ..
theorem rephase_test (A : QP) (X : Mob G) (w : Legs (Shore G m)) : rephase A X m w=waveFact A (net w)*X m w := rfl

theorem weave_token {b : Bool} (hX : Sturdy b X) (hY : Sturdy b Y) : Sturdy b (weave X Y) := by
   refine ⟨fun n K hK=> ?_,fun ht l=> ?_ ⟩
   · unfold weave; rw [circle_prod,hX.turn n K hK,hY.turn n K hK]
   simp only [weave,scattered,scatter_up,hX.grows,hY.grows]

theorem onPlane_comp (he:m≤n) (p : SectorP n) : onPlane n p=onPlane m (Cl he p) := by funext i; rfl

theorem fact_turn (A : QP) (K : Spin (Arts.L m)) (hK : within false K) (p : SectorP m) : waveFact A (K.turn p)=waveFact A p := by
   let h:= Nat.zero_le m
   obtain he:= K.rad (Left h A) p; rw [hK rfl _, farApart h (Left h _),farApart h (Left h _), leftCl, Cr_down,
     Arts.pair_zero,Arts.pair_zero,add_zero,add_zero] at he
   exact congr_arg (fun x:ℝ=> Complex.exp (Complex.I*x)) he

theorem rephase_token (A : QP) (hX : Sturdy false X) : Sturdy false (rephase A X) := by
   refine ⟨fun m K hK=> funext fun l=> ?_, fun h w=>?_⟩
   · let V:= flagS K G; let v:=net l; let u:= waveFact A v
     rw [V.offset (v:=rephase A X m) (w:=u • X m) (u:=v) (l:=l) (by
       intro i hi; change net i=K.turn v at hi; rw [rephase_test,hi,fact_turn A K hK]; rfl) rfl, map_smul,hX.turn m K hK]
     rfl
   rw [rephase_test,rephase_test,hX.grows,lifts_net]
   unfold waveFact; rw [onPlane_comp h,leftCl]

theorem weave_price (hX : fell δ a f) (hY : fell δ b g) : fell δ (a*b) (fun i=> weave (f i) (g i)) := by
   intro m E _ _ _ w
   unfold fieldVal weave; simp_rw [scattered, sail_scatter]; exact gather_bound w (fun l r _=> (hX m E l).mul (hY m E r))

theorem rephase_price (hX : fell δ a f) (hp : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (Arc.path δ).full.Le (fun i (_:E)=>‖P i‖) (fun _ _=>1)) : fell δ a (fun i=> rephase (P i) (f i)) := by
   intro m E _ _ _ w; unfold fieldVal; simp_rw [rephase_test,sail_net]; exact pulse_bill (onPlane _ ∘L net w) (hX m E w) (hp E)

theorem form_weave (hX : Form0 false X) (hY : Form0 false Y) : Form0 false (weave X Y) :=
   ⟨by convert! weave_price hX.price hY.price using 1; ext; simp, weave_token hX.token hY.token⟩

theorem form_rephase (hX : Form0 false X) (A : QP) : Form0 false (rephase A X) :=
   ⟨rephase_price (P:=fun _:Unit=>A) hX.price (fun _ _ _=> ⟨_, (by positivity:0<1+‖A‖),0,fun _ _ _=>by simp⟩),rephase_token A hX.token⟩

-- for use on multi-pin histories
variable {F H : ℂ→Mob G}
theorem weave_hill (hX : hill R F) (hY : hill R H) : hill R (fun z=> weave (F z) (H z)) := by
   intro m w z hz; unfold weave; simp_rw [scattered];
   have he (w : Legs (Shore G m)) (U:ℂ→Shared (Shore G m) ℂ) (hk : ∀ l r, DifferentiableAt ℂ (fun z=> U z l r) z) : DifferentiableAt ℂ (fun z=> scatter (field parity) w (U z)) z := by
     induction w generalizing U with
     | nil=> exact hk [] []
     | cons i l ih=> exact ih _ (fun l r=> DifferentiableAt.add (hk (i::l) r) ((hk l (i::r)).const_mul _))
   exact he w _ (fun l r=> (hX m l z hz).mul (hY m r z hz))

theorem rephase_hill (hX : hill R F) (A : QP) : hill R (fun z=> rephase A (F z)) := fun m w z hz=> (hX m w z hz).const_mul _
theorem hol_weave (hX : Hol R F) (hY : Hol R H) : Hol R (fun z=> weave (F z) (H z)) where
   price c Z hz he := by convert! weave_price (hX.price c Z hz he) (hY.price c Z hz he) using 1; ext; simp
   top := weave_hill hX.top hY.top
theorem hol_rephase (hX : Hol R F) (A : QP) : Hol R (fun z=> rephase A (F z)) where
   price c Z hz he := rephase_price (P:=fun _=>A) (hX.price c Z hz he) (fun _ _ _=> ⟨_, (by positivity: 0<1+‖A‖), 0, fun _ _ _=>by simp⟩)
   top := rephase_hill hX.top A
end YM.MS.ScaleForest
