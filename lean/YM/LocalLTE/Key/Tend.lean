import YM.LocalLTE.Key.Gifts
/-! Curve witness & receipts. -/
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
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J
open Collection.Price LocalLTE.FrameBox
section generic
variable {G:Gauge} {c:Side} (X:Listing G c) (P':BudgetPoint)(t m u:ℕ)(V:Price.Tour X t)
    (hp:u<t)(hh:2 ≤ u)
-- generic any θ chosen homestead. Tower.
include hp hh
def garden : Price.Tour (Marlin.pluck P' (Marlin.lodge X t m)) t:= by
    let f : Civ c→RegularAddress c:=fun i=> Sum.elim X.reg (Marlin.sea t) i
    let g : ∀ i:Civ c, Option (Price.Art (f i) t) := fun i=> match i with
      | .inl i=> V i
      | .inr i=> Option.some (Price.Art.turn ⟨cane i.2,u,rfl,hp,hh⟩ i.1 (f (.inr i)) (a:=leap t i.2) rfl rfl) -- name
    exact fun i=> g (Marlin.leanU c i)
    -- unfold f; point transport.
lemma portrait {k:ℕ} {κ K:ℝ}(h:Reliable G κ K)(W:ℕ→ Config G c→ ℝ)(f:Site c → Config G c→ℝ)(hx: ∀ i:Site c,Replicated (cane i) u κ (pie k+1) (f i))(hp': Price.Portrays X t κ k W V): Price.Portrays (Marlin.pluck P' (Marlin.lodge X t m)) t κ k (Sum.elim W (Song.choir f) ∘ Marlin.leanU c) (garden X P' t m u V hp hh):=by
    let g := Sum.elim W (choir f)
    -- dependent use rec.Cases BEFORE intros.
    let Lo : Civ c→RegularAddress c:=Sum.elim X.reg (Marlin.sea t); let q : ∀ i:Civ c, Option (Price.Art (Lo i) t):=fun i=> match i with
      | .inl j=>V j
      | .inr i=> Option.some (Price.Art.turn ⟨cane i.2,u,rfl,hp,hh⟩ i.1 (Lo (.inr i)) (a:=leap t i.2) rfl rfl)
    have hu i (h:q i=Option.none): g i=0 := by
       rcases i with i|i; exact hp'.stays i h
       simp only [q,reduceCtorEq] at h
    refine ⟨fun i h=>hu _ h,fun i A hh'=>?_⟩
    have h j (p:Price.Art (Lo j) t)(ht:q j=Option.some p): Replicated p.grove p.radius κ (pie k+1) (g j):= by
       rcases j with j|j; exact hp'.frame j p ht
       let y:=Price.Art.turn ⟨cane j.2,u,rfl,hp,hh⟩ j.1 (Lo (.inr j)) (a:=leap t j.2) rfl rfl
       have hz:y=p:=Option.some.inj ht; subst p; exact Price.rp_scale _ _ (Price.rotatedG (a:=leap t j.2) _ _ j.1 _ rfl rfl h (hx _))
    exact h (leanU c i) A hh'
omit hp hh
-- budget lift porch.
variable (Cur:ℕ→ Config G c→ℝ)(t' f':Trio.Offer G c)(d:Collection.Source G c){e₀ w' :ℝ}
lemma enter (h:Meadow.Budget P' X.reg (d.logRead-Cur) e₀)(hh: Meadow.Budget P' (leap t) (t'-f') w') (v: Trio.Offer G c) :
    Meadow.Budget P' (Marlin.pluck P' (Marlin.lodge X t m)|>.reg) ((poursP P' (Marlin.lodge X t m) (bison d t' v)|>.logRead) - (Sum.elim Cur (Song.choir f') ∘ Marlin.leanU c)) (e₀+turnFee P' *w'):= by
      let d':=Magnet.seed (d.logRead-Cur); let U:=Marlin.lodge X t m
      rw [show (poursP P' U (bison d t' v)|>.logRead) -(Sum.elim Cur (Song.choir f') ∘ Marlin.leanU c)=(bison d' (t'-f') v|>.regular) from ?_]; swap
      · funext i V; change Sum.elim d.logRead (choir t') (Marlin.leanU c i) V - Sum.elim Cur (choir f') (Marlin.leanU c i) V=Sum.elim d'.logRead (choir (t'-f')) (Marlin.leanU c i) V; cases Marlin.leanU c i; rfl
        exact (mul_sub ..).symm
      exact Marlin.reg_bison X t m d' _ _ h hh
end generic
namespace Career
local notation "Ω"=> F.hearth H
local notation "d'"=> W.crew H m*radiusB x₀
local notation "P₀"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "t₀"=> (F.school H W k' tag)
local notation "V₀"=> (F.porch H W k' tag)
local notation "κ₀"=> H.κ
local notation "Z₀"=> Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "S"=> (A.B.a.S)
include F
set_option linter.unusedSectionVars false in
lemma existZ : 2 ≤ z ∧ Z₀ < d' := by
    have he := Trail.breadth H W (m:=m) (n:=n); unfold Trio.base at *; omega -- n unused, include A?
abbrev billow : Price.Tour t₀ d':= garden V₀ B d' d' z (F.trout H W k' tag) (Career.existZ H F W).2 (Career.existZ H F W).1
lemma wealthy (x:ℝ)(j:ℕ): Price.Portrays t₀ d' H.κ j (F.fruits H W k' tag x j) (F.billow H W k' tag) :=by
    apply Mallow.portrait (P':=B) _ _ _ _ _ _ _ H.paid.choose_spec _ _ (?_) (Career.sold H F W k' tag x j); intro i; exact ⟨_,rfl⟩
end Career
end YM.PhysicalNext.Repeat.Mallow
