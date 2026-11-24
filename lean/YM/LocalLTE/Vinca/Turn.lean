import YM.LocalLTE.Vinca.Stock
import YM.MergeProof.Volley
/-! Key onto designed Career.C.Pull.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vinca
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
variable (Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
structure Candlestick (R:Rep G StartSite) (L:Side) (C w t:ℝ)(T:Heading F) (A:Wing→Prop) (P:Gateway F Y R WorkSite) : Prop where
   main (j:F.Index): j≠0 → let v:=Size.axis F j; let Z:=Extra.Histories.primary (0:Site StartSite) v
    Ink B H N p i Y (Z.exponentialEntry 0 B R) 0 0 Q A (Z.density 0 B R) (T.leads L v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (Bid.vowel F L (F.core v))) t (P.core j)
   regular (f:g₀)(b:Support StartSite)(x:ℝ): let u:=(R).p.mass b x; ∀ (h:RegFit R 0 d Y b f)(hv:(R).p.supBounds 0 b f x), Ink B H N p i Y (masked (R).p.threshold b f) 0 0 Q A (salary R b f) 0 (w*u) (w*u) (2*u) (P.reader f b x h hv)
   forced (f:g₀)(j:ℕ)(x:ℝ): let u:=(R).p.mass ((R).activities.forced j).support x; f≠0 → A (.gasKey j)→ ∀ (h:SlotFit R 0 j f)(hv:∀ U,‖f U‖≤x), Ink B H N p i Y 0 (exactGas (R).activities j f) 0 Q A (Extra.Histories.fare R j f) 0 (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*u) (P.flag f j x h hv)
   map_norm v : F.coeffSize (T.map v) ≤ C * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ C * F.coeffSize v
variable {Q}{T:Heading F}{A:Wing→ Prop}{a t u:ℝ}{L:Side}{R:Rep G (H.S.side (i+1) p)}
def sway (R:Rep G (H.S.side (i+1) p))(he:Old=R) (X:Gateway F Y R WorkSite):Gateway F Y Old WorkSite:=he.symm ▸ X
lemma kindles (he:Old=R) (h:H.S.block i=L)(X:Gateway F Y R WorkSite) (hp:Candlestick B H N p i Y Q R L a t u T A X) : Key B H N p i Y Q (sway H N p i Y R he X) a t u T A:=by
   subst L R; exact ⟨hp.main,hp.regular,hp.forced,hp.map_norm⟩
end YM.LocalLTE.Vinca
