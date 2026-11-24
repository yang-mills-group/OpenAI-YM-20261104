import YM.LocalLTE.Crafts.Bands
import YM.LocalLTE.Newborn.Contract
import YM.LocalLTE.Estate.Logs
import YM.LocalLTE.Pool.Dawn
import YM.LocalLTE.Bonnet.Canopy
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
variable {p:ℕ}(W:Trail H p)(M:Preview H)(v:Bolt A)(hv:Made H W M v)
open Progress.DirectedRecipe Averaging LocalLTE.FrameBox Price
namespace Career
variable (k':ℕ)(R' R'': Rep G (A.B.a.S.side (m+1) n))
local notation "tag'"=> Mallow.spread A.B.a N p n (m+1)
local notation "t₀"=> F.school H W k' tag'
set_option quotPrecheck false
end Career
-- grade RESIDUE.Old K always transmitted. no repetitive.Fittings.Sym
open Rack Ovens Ovens.Pipes
section skim
variable {G:Gauge}{n:Side}(A:Activities G n)(X: Pipes G n)(t:Tap G n) (k:ℕ→ℕ) {s:Signed}{a:Site n}
lemma w_move (f:Equiv.Perm ℕ)(h:∀ i,X.reg (f i)=regMap (destination s a) (X.reg i))(hr:∀ i,t.regular (f i)=t.regular i∘ pull s a)(hf:A.reg=(drawer G n|>.reg))(he:A.E=stuff (upE X) t.regular) (hk:∀ i, k (rearrange (regularKeys n) (regMap (destination s a)) f i)=k i) (M:Nonempty (A.Moves s a)) : ∃ y:A.Moves s a, ∀ i,k (y.ep i)=k i:=by
    let u:= regMap (destination s a); let K:=rearrange (regularKeys n) u f; let W:= (drawer G n); let Y:=M.some
    have hh i:W.reg (K i)=u (W.reg i):=congr_arg Prod.fst (stocked (regularKeys n) u f i); have hz i:A.reg (K i)= u (A.reg i):=by rw [hf]; exact hh i
    let R:=upE X; have hP i: K (R i)=R (f i):= move_stock _ _ f X.reg (fun i=> (h i).symm) i
    refine ⟨{Y with ep:=K, reg_site:= fun i=> congr_arg RegularAddress.site (hz i), reg_support:= fun i=> congr_arg RegularAddress.support (hz i), valuesE:= fun i U=> ?_},hk⟩
    rw [he]; by_cases h:i∈Set.range R; swap; · rw [blank _ _ (unused hP h), blank _ _ h]; rfl
    obtain ⟨i,rfl⟩:=h; rw [hP,stuffed,stuffed]; exact congr_fun (hr i) U
-- `hp` unused!
end skim
namespace Career
variable (k' :ℕ)
local notation "t'"=> Mallow.spread A.B.a N p n (m+1)
local notation "X'"=> (F.barn H W k' t')
set_option quotPrecheck false
local notation "V!" x=> F.Voy H W k' t' k x
lemma coil (x:ℝ) (b:Signed) (o:Site (A₀)) (hC:Nonempty ((F.Voy H W k' t' k x).activities.Moves b o)) : ∃ q:(F.Voy H W k' t' k x).activities.Moves b o, ∀ i, Price.grade (A₀) p (q.ep i)=Price.grade (A₀) p i:=by
    let V₀:=(V! x).activities; let U:= F.tongue H W k' t' k x
    let D:= (A₀); let e:= numbering (Price.Rol p D); let u:= Song.whirl (ι:=Fin (p+2) × EKey D) b o; let f:=(e.trans u).trans e.symm; let p':=(B)
    let ts:= F.school H W k' t'; let Z := Price.sands B (A.B.kin.path N m) ts p -- A local conflicts
    let F':= F.index H W k' t' k x; let P:= Price.silt (A.B.a.params m|>.clip) (A.B.kin.path N m) ts F' p (delta (ts.read F')) γ (F.goals H W k' t' x)
    have h i:e (f i)=u (e i):=Equiv.apply_symm_apply ..; have he i: Price.pocket D p (f i)= Price.pocket D p i := by change (e (f i)).2.1.val= _; rw [h]; rfl
    refine Mallow.w_move V₀ X' U (Price.grade (A₀) p) f (fun i=> ?_) (fun i=> ?_) rfl rfl (fun i=> ?_) hC -- e hp removed
    · change Song.revolve Z (e _)= _; rw [h]; refine Progress.DirectedRecipe.reg_ext (Song.spirit _ P b o (e i)|>.1) (Song.spirit _ P b o (e i)|>.2.1)
    · change Song.choir P (e _)=_; rw [h]; exact Song.spirit Z _ b o (e i)|>.2.2
    unfold Price.grade; rw [Progress.DirectedRecipe.stocked]; cases hz:(regularKeys (A₀) i).2; next j=> exact he j
    rfl
end Career
end YM.PhysicalNext.Repeat.Mallow
