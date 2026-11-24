import YM.FormalOPE.RG10.OpenSlots.Pull
/-!
 # Ledger evolution (including denominator).
 weight and poles before restoring Laurent powers. Multiply tickets to value inserted pairs etc.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G: Gauge} {c f n: Side}
variable {S: StepData c f} {L: Fabric G c} {P:Inside S.ratio}
variable {H:S.patch.Branches S.kernel G} {hf:_root_.Even f.val}{t:S.Choices} {C:Cloth L}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ω"=> Field (Cloth.choose T0)
local notation "F"=> Cross (G:=G) S P
local notation "B"=> Field C.choose
local notation "κ"=> exchange (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "π"=> spool (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Γ"=> layer S H t hf L
open Quadratic
-- free of P.C etc implicit future variables. use on any step S.
 def Update (P:Inside S.ratio)(t:S.Choices)(J:ChartRatio G)(w:PowerSeries ℝ)(U:Unmasked G f) (h:(core (gated P U t w)).RespectsPrice): Unmasked G c where
 Q:= reduced _ h
 W:= uptake _ (tangent G (Index S P)) h (receipt P t J w U)
 def Broadcast (P:Inside S.ratio)(t:S.Choices)(J:ChartRatio G)(w:PowerSeries ℝ)(U:Unmasked G f) (h:(core (gated P U t w)).RespectsPrice)(A:Ticket (Cross (G:=G) S P × Flats G c)): Ticket (Flats G c):= fit _ (tangent G (Index S P)) h A (receipt P t J w U)
lemma funded {J:ChartRatio G}(hj: LocalRatio J)(w:PowerSeries ℝ){U:Unmasked G f}(u: incline U.W)(h:(core (gated P U t w)).RespectsPrice): incline (Update P t J w U h).W:= Quadratic.upright _ (tangent G (Index S P)) h (along hj w u)
namespace Bank
variable {J:ChartRatio G}{U:Unmasked G f}
variable {z:(layer S H t hf L).Cost→PowerSeries ℝ}
variable {Λ' : Law (Field (Cloth.choose (Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C)))} -- try macro stale; no
local notation "μ"=> tangent G (Index S P)
lemma one_sided {Λ:Law Ω}{V:Ticket Ω}(h:Bank T0 J z U Λ V)(A:Ticket (F× Flats G c)):
 reclose Λ d μ (boost κ A)= boost (castAt C) (uptake _ μ h.respects A):= by
 apply PowerSeries.ext; intro i; apply Subtype.ext; ext1 y
 unfold reclose boost Quadratic.uptake throughPrice;
 simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_map,coeff_mk,LinearMap.toAddMonoidHom_coe]
 change (partialMean Λ d μ (translation κ (coeff i A))).val y= (integrateP _ μ h.respects (coeff i A)).val (castAt C y)
 rw [displayed, integrateP_display,h.score, RespectsPrice.pinpoints _ h.rad]; apply congr_arg ((fast Λ d).average μ); funext x; unfold translation; simp
lemma gathered {Λ:Law Ω}{V:Ticket Ω}(hj:LocalRatio J)(h:Bank T0 J z U Λ V)(A:Ticket (F×Flats G c)):
 reclose Λ d μ (V*boost κ A)= boost (castAt C) (uptake _ μ h.respects ((receipt P t J (z none) U)*A)) * (tissue J C.choose.Bulk * remExponent C (z∘some)):= by
 let V₀:= receipt P t J (z none) U; let R:= tissue J C.choose.Bulk * remExponent C (z∘ some)
 conv_lhs => rw [h.shipments hj]
 change reclose Λ d μ (boost _ V₀ * Ancestor R * _) = _ * R;
 rw [mul_right_comm,← map_mul (boost κ), pullOut,h.one_sided]
lemma confirmation {Λ:Law Ω}{V: Ticket Ω}(hj:LocalRatio J)(h:Bank T0 J z U Λ V): Bank C J (z∘some) (Update P t J (z none) U h.respects) (rest Λ d) (reclose Λ d μ V) where
 main y:=h.lower y
 price:=by
   have H:= h.gathered hj 1; simp only [_root_.map_one,mul_one] at H; rw [H, ← mul_assoc]; rfl
lemma imprint {Λ:Law Ω}{V:Ticket Ω}(hj:LocalRatio J)(h:Bank T0 J z U Λ V)(u: incline U.W) (A:Ticket (F×Flats G c)):
 delivered Λ d μ (boost κ A) V=boost (castAt C) (Broadcast P t J (z none) U h.respects A):= by
 have he: incline V:= readyI (H:=hj) T0 J _ U h u
 let R:= tissue J C.choose.Bulk * remExponent C (z∘some)
 let W:= receipt P t J (z none) U
 apply (worth (born_transfer Λ d μ he)).mul_left_cancel
 rw [junior Λ d μ _ he,h.gathered hj,(h.confirmation hj).price, mul_assoc (boost (castAt C) _ ) (tissue J C.choose.Bulk)]
 unfold Update Broadcast; rw [mul_right_comm (boost (castAt C) _), ← map_mul (boost (castAt C)),Quadratic.fit_eq _ _ _ _ _ (along hj (z none) u)]
end Bank
end YM.FormalOPE.RG10.OpenSlots
