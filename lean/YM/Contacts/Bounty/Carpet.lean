import YM.Contacts.Bounty.Moment
/-! # Carpet.Vehicle. combine stage targets.Loom exhibit geometry. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Bounty.Trophy.Lore
open AnalyticBridge VerifiedReset Collection Quotes Revest Flute Outlay
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Lattice Wilson RG Pressure Ovens Ovens.Pipes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam Model
open Pulse ConnectedActivityE6 Testing SectorMeasure Presented Coat Blaze Blaze.March
open Boulevard Poetry Song Pane Trio Slide Push.Uniform Height PriceCompiler
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {M: Metals G}{D:Rolls M.p}{A:Alloy M D} {B:Factor A} {F F':bore G}
variable {c f c₀:Side}{i j k m n N o:ℕ} {q l r v α β t s e E':ℝ}
local notation "x" => A.B.a.clock.hatBeta m
local notation "y" => betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "C" => B.target J I
local notation "P" => A.B.a.budget m
local notation "P'" => A.B.a.budget (m+1)
local notation "ωP" => B.expense J I
local notation "p" => A.B.a.params m
local notation "u₀" => M.p.profile I
local notation "L" => D.L J
local notation "η" => B.shape.μ J I
local notation "E" => B.shape.o J I
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "z" => radiusB x
local notation "ℓ₀" => (C).halo
local notation "d" => dim ℓ₀ o
local notation "K₀" => Trio.base d z
local notation "w₀" => Trio.tent d z
local notation "T" => Poetry.studio ℓ₀ z (P').B o
local notation "L₀" => A.B.a.S.block m
abbrev Oaks (B:Factor A)(m o:ℕ) (i:Stars):Side:= fence (cape A B m o) (radiusB (A.B.a.clock.hatBeta m)) i
abbrev Lumber (B:Factor A)(m o:ℕ)(i:Stars):Side:= Oaks B m o i * (A.B.a.S.block m)
abbrev slit (B:Factor A) (m o:ℕ) (i:Stars): (Lumber B m o i).val=(Oaks B m o i).val*(A.B.a.S.block m).val:= rfl
abbrev canvases (B:Factor A) (m o:ℕ) (i:Stars) : (Oaks B m o i).val= 2*(Trio.tent (cape A B m o) (radiusB (A.B.a.clock.hatBeta m))+i.val):= rfl
section loom
abbrev Tint (F:bore G)(k N:ℕ) (A:Alloy M D) (m:ℕ) (q:ℝ): Offer G c:= integrated (A.B.a.budget m) F (A.B.a.params m).clip (A.B.kin.path N m) k q
abbrev Savior (A:Alloy M D)(m:ℕ)(Y:bore G)(k N:ℕ) (ε :ℝ) := let U:=A.B.a.budget m; let K:=(A.B.kin.path N m); let b:=(A.B.a.params m).clip; LocalOn (Lattice.box U.B) (written U Y b K k ε)∧ ∀ c:Side,10*U.B<c.val→Salary U (Tint (c:=c) Y k N A m ε) (Outlay.ν (A.B.a.clock.hatBeta m))
end loom
variable (H:Buzz B o m l) (hm:m<N) (hp:Decent (A.B.a.params m).clip (A.B.a.budget m)) (ht: Geo.Width (A.B.a.budget m) (A.B.a.params m).clip (A.B.a.params m).width)
   (hα:|q-A.B.kin.alpha N m|≤ Outlay.potion (A.B.a.clock.hatBeta m))
local notation "Ω" => (veil l y)
local notation "U" => (fun i=> Trophy.drag A (slit B m o i) k F β (N:=N))
local notation "N₀" => Oaks B m o
structure Tiles (B:Factor A)(o m N:ℕ)(F : bore G) (k:ℕ)(β:ℝ) where -- polymPu.Binder
   splice (i:Stars): Chartlet B.shape A N m (slit B m o i) (Trophy.drag A (slit B m o i) k F β (N:=N))
   owns i : SeekR B.shape A N m (slit B m o i) (splice i)
variable (Y:Tiles B o m N F k β)
local notation "W" => (fun i=> Pales.pub (Pane.orchestra A N (slit B m o i)) k F P' β)
local notation "M'" => Tint F' k N A m (β+q) -- c implicit? expected
abbrev carpet (F':bore G)(i:ℕ)(q:ℝ)(s:Stars): Offer G (Oaks B m o s):= Poetry.barony o (Y.splice s) (W s) O i (β+q) q - Tint F' k N A m (β+q) -- notation bug .M' shadow
-- input elevation predicate for all
abbrev Dawn (B:Factor A)(o m N:ℕ)(F Y:bore G)(k:ℕ)(β q l:ℝ):=∀ i:Stars,Elevation A N m (slit B m o i) (Trophy.drag A (slit B m o i) k F β (N:=N)) Y k q (veil l (betaF G (A.B.a.clock.hatBeta m) (D.L (A.B.a.clock.J (m+1)))))
namespace Buzz
include H
lemma sizing : (P').B ≤ 2*(P).B∧1≤z∧0<T∧(P).B ≤ T∧ 2*T≤w₀ ∧ certificate A B m o≤ w₀:= by
   have hx: (P').B≤2*z:= by change radiusB (A.B.a.clock.hatBeta (m+1)) ≤2*z; rw [PriceCompiler.beta_eq A.B.valid]; exact H.cash.cover
   have hp:1≤ z:= (P).B_pos; have hv:= Lore.ceiling (B:=B) (o:=o) (m:=m) hx; have hh:8*T≤ certificate A B m o:=Nat.le_add_right ..; have hy:(P).B ≤ T:= (Nat.le_add_left  ..)|>.trans' (by change z≤ _; omega) -- binder
   exact ⟨hx,hp,Nat.pos_of_ne_zero (by change z≤ T at hy; omega), hy,Nat.le_trans (by omega) (hh.trans hv),hv⟩
lemma trunks (i:Stars): certificate A B m o ≤ (N₀ i).val ∧ 10*z < (N₀ i).val ∧ 10*(P').B < (Lumber B m o i).val∧ 100*(1+z) ≤ (N₀ i).val:= by
   let c:= certificate A B m o; let b i:= N₀ i; have ht:(b i).val=2*(w₀+i.val):=rfl; have hh:(b i).val ≤ (Lumber B m o i).val:=Nat.le_mul_of_pos_right _ ((A.B.a.S.block m).pos); have hx:200*(1+z+(P').B+z)≤ c:= Nat.le_add_left ..; have hp : c ≤ w₀:= H.sizing.2.2.2.2.2; change c≤ (b i).val ∧ 10*z < (b i).val ∧ _ ∧ 100*(1+z)≤(b i).val; omega
lemma realWall (n:ℕ): 2*K₀ < (A.B.a.S.side m n).val∧ certificate A B m o≤(A.B.a.S.side m n).val:= by
   have ht:= wholeV (n:=n) H.support; change 2*(w₀+5)<_ at ht; exact ⟨ht,(H.sizing).2.2.2.2.2.trans (by omega)⟩
variable (hF:Trophy.Pay A m F k N β)(hb:β∈band A.B.a (m+1))
include hm hb hF
lemma ceramics : Nonempty (Tiles B o m N F k β):= by choose Y hY using fun i:Stars=> begs A B (slit B m o i) hm (H.trunks i|>.2.2.2) (H.trunks i|>.2.2.1) hb hF; exact ⟨Y,hY⟩
variable (hT:Savior A m F' k N (β+q))
omit H hm hb hF
include hT
lemma tintC : Trio.Compatible (Tint (c:=c) F' k N A m (β+q)) (Tint (c:=c₀) F' k N A m (β+q)) P z:= by
  intro ix iy u v h₁ h₂ h; rw [Tint,Tint,← codify,← codify]; exact hT.1 _ _ h
-- include hT
section mini
include H
lemma apart : Trio.Compatible (Tint (c:=c) F' k N A m (β+q)) (Tint (c:=c₀) F' k N A m (β+q)) P T := by
  intro ix iy u v h₁ h₂ h; refine tintC hT ix iy u v h₁ h₂ ?_; refine fun e he ht=> h e ?_ ?_; all_goals exact (GridApprox.box_larger (by assumption) (H.sizing).2.2.2.1) -- fix shadow notation x,y!!
end mini
end Buzz
end YM.Contacts.Bounty.Trophy.Lore
