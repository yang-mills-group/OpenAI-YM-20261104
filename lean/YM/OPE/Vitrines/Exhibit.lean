import YM.MergeProof.Visit
import YM.OPE.Vitrines.Budget
import YM.MergeProof.Volley
/-! # Price with +2 reserve, adapted from MergeProof/{Chalet,Wallet,Volley,Visit} -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat 
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "y"=> H.levels.clock.forcedAllowance i
structure Lucent (f:g₀)(P:Coefficient F WorkSite)(lead:F.Coeff)(c v:ℝ) :Prop where
    format:P.Format 0 Y Rout
    agrees:P.density 0 B Rout= blast H N p i d f
    leadP:orbitCost F*F.coeffSize (P.x-lead)≤c
    future:∃ a b:ℝ, Tab P 0 Rout (kappa H i) a b ∧ turnCost (Rout).p.order (Rout).p.power*a+b ≤ v
    pale:∃ a:ℝ, Blown P 0 Rout a ∧ turnCost (Rout).p.order (Rout).p.power*a ≤ v
variable {B H N p i Y}{X:ℕ→Support (H.S.side i p)}{M: Local.Raw F (H.S.side i p)}{f:Config G (H.S.side (i+1) p)→ℂ}{lead:F.Coeff}{w t r:ℝ}
lemma Lucent.original {f:g₀}{P:Coefficient F WorkSite}{z:F.Coeff}{a b:ℝ}
    (h:Lucent B H N p i Y f P z a b): Gig B H N p i Y f P z a b:=⟨h.format,h.agrees,h.leadP,h.future⟩ -- B implicit? block after variable declarations
lemma growB (h:Fancy B H N p i Y f X M lead w t r) (hx:H.Conv N p i)(he:Readable Y B (Rout).p WorkSite w): ∃ P:Coefficient F WorkSite,
    Lucent B H N p i Y f P lead t r ∧ Attainment (Rout).p 0 (coda B Y 0 X M Rout) r ∧
      profile (Rout).activities P.forced= profile (Rout).activities M.forced + hook (Rout).activities (Rout).p.threshold (coda B Y 0 X M Rout):=by
   obtain ⟨a,b,c,⟨h₁,h₂⟩,⟨S⟩,hv,⟨pQ,q,hq,h₃⟩,hA,hC⟩:=h; let Z:= mint S M Y
   have hh:= (vigor hq h₁ he)
   rw [h₃] at hh
   have hκ:0<kappa H i:= Real.sqrt_pos.mpr (forcedPos ..)
   have hp:Tab Z 0 Rout (kappa H i) a (b+c):=tab_mint S h₁ hx.good hκ he hv
   have htX:1≤ turnCost (Rout).p.order (Rout).p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   refine ⟨Z,⟨usage S h₁ hx.good he,(value_mint S h₁ hx.good hκ he hv).trans h₂,?_,⟨_,_,hp,hA⟩,a,h₃ ▸ Blown.deck S h₁ he hq,(le_add_of_nonneg_right hp.second).trans hA⟩,stackFee hh ((le_mul_of_one_le_left hp.first htX).trans ((le_add_of_nonneg_right hp.second).trans hA)),budgetProfile S hv h₁ he hx.good hκ⟩
   obtain ⟨f,e,h1,h2,h3⟩ | hP := hC
   · exact le_trans (mul_le_mul_of_nonneg_left (sensor S h₁ he hv h1 h2) (zero_le_one.trans (orbitCost_one_le F))) h3
   exact le_trans (mul_le_mul_of_nonneg_left (size_mint S h₁ he hv lead) (zero_le_one.trans (orbitCost_one_le F))) hP
end YM.MergeProof
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
-- sockets. Uses Chart selected for proofs. turnset X budget.
def CreamBid (α : Config G StartSite→ℂ)(ρ:Res G StartSite) (δ:ℂ) (Q:GaugeDoor Old Rout)(A:Wing→Prop)(f:g₀)(lead:F.Coeff)(c t u:ℝ):Prop:=∃ P:Coefficient F WorkSite, Lucent B H N p i Y f P lead c t ∧ Tale A 0 0 ((↑(Lℓ).val:ℂ)^d) α ρ (profile (Rout).activities P.forced) δ u t Q

variable (Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
-- AND unit private. C0 root cost for main axis; cQ≈Cred.Cover. calendar.
structure Supernova (C w t:ℝ)(T:Heading F) (A:Wing→Prop) : Prop where
   -- insert Q binder
   main (j:F.Index): j≠0 → let v:=Size.axis F j; let Z:=Extra.Histories.primary (0:Site StartSite) v
    CreamBid B H N p i Y (Z.exponentialEntry 0 B Old) 0 0 Q A (Z.density 0 B Old) (T.leads Lℓ v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (Bid.vowel F Lℓ (F.core v))) t
   regular (f:g₀)(b:Support StartSite)(x:ℝ): let u:=(Old).p.mass b x
    RegFit Old 0 d Y b f→ (Old).p.supBounds 0 b f x→ CreamBid B H N p i Y (masked (Old).p.threshold b f) 0 0 Q A (salary Old b f) 0 (w*u) (w*u) (2*u)
   forced (f:g₀)(j:ℕ)(x:ℝ): let u:=(Old).p.mass ((Old).activities.forced j).support x
    f≠0 → A (.gasKey j)→ SlotFit Old 0 j f→ 0≤x → (∀ U,‖f U‖≤x) → CreamBid B H N p i Y 0 (exactGas (Old).activities j f) 0 Q A (Extra.Histories.fare Old j f) 0 (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*u)
   map_norm v : F.coeffSize (T.map v) ≤ C * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ C * F.coeffSize v
-- version parameter alternate docks Rin & E given by equalities. Syntax.
end YM.MergeProof
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
variable (Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
-- AND unit private. C0 root cost for main axis; cQ≈Cred.Cover. calendar.
structure SwanDive (R:Rep G StartSite) (L:Side) (C w t:ℝ)(T:Heading F) (A:Wing→Prop) : Prop where
   -- insert Q binder
   main (j:F.Index): j≠0 → let v:=Size.axis F j; let Z:=Extra.Histories.primary (0:Site StartSite) v
    CreamBid B H N p i Y (Z.exponentialEntry 0 B R) 0 0 Q A (Z.density 0 B R) (T.leads L v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (Bid.vowel F L (F.core v))) t
   regular (f:g₀)(b:Support StartSite)(x:ℝ): let u:=(R).p.mass b x
    RegFit R 0 d Y b f→ (R).p.supBounds 0 b f x→ CreamBid B H N p i Y (masked (R).p.threshold b f) 0 0 Q A (salary R b f) 0 (w*u) (w*u) (2*u)
   forced (f:g₀)(j:ℕ)(x:ℝ): let u:=(R).p.mass ((R).activities.forced j).support x
    f≠0 → A (.gasKey j)→ SlotFit R 0 j f→ 0≤x → (∀ U,‖f U‖≤x) → CreamBid B H N p i Y 0 (exactGas (R).activities j f) 0 Q A (Extra.Histories.fare R j f) 0 (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*u)
   map_norm v : F.coeffSize (T.map v) ≤ C * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ C * F.coeffSize v
variable {H N p i Y B Q}{L:Side}{C w t:ℝ}{T:Heading F}{A:Wing→Prop}
lemma turnoutB {R}(he:Old=R)(h:H.S.block i=L)(hp:SwanDive B H N p i Y Q R L C w t T A): Supernova B H N p i Y Q C w t T A:=by
   subst L R; exact ⟨hp.main,hp.regular,hp.forced,hp.map_norm⟩
-- may `Heading` binder. and accidental notation
end YM.MergeProof
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
section
-- re-use score explicitly.
variable {R:Rep G (H.S.side i p)}{E:Rep G (H.S.side (i+1) p)}
variable (he : H.rep N p i=R) (h : H.rep N p (i+1)=E)
   (Q:GaugeDoor E R)
-- move door definition for any m, oriented actions. Maintain casts. on any layout.
lemma borderB (A:Wing→Prop)(α:g₀)(ρ:Res G StartSite)(f:g₀) (a t u:ℝ)(lead:F.Coeff)(L:Side)(hw:H.S.block i=L)(P:Coefficient F WorkSite)(hq:Lucent B H N p i Y f P lead a t)
    (hp:Tale A 0 0 ((L.val:ℂ)^d) α ρ (profile R.activities P.forced) 0 u t Q): CreamBid B H N p i Y α ρ 0 (duet _ _ _ _ he h Q) A f lead a t u:=by
   subst L; exact ⟨P,hq,peels H N p i he h Q A α ρ _ _ _ _ _ _ _ hp⟩
end
end YM.MergeProof
