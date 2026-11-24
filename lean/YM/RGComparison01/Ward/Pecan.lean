import YM.RGComparison01.Marks.Fiord
import YM.RGComparison01.Ward.Temper

/-!
# Reserve larger region for rooted auxiliary lifts

 Keep Holden/Stellar small radii also for direct coefficient requests.
 Both sets allocated in one calendar. Only sufficient demanded β range. Charge
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ward
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Tensor WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G:Gauge}{c L:Side}{j k :ℕ}{p r u d v :ℝ}
local notation "ρ"=>royalty G
namespace Duplex
variable (D:Duplex G k)(b:ℕ)
abbrev town (b:ℕ)(t:ℝ) := Trio.fence b (radiusB t) (0:Slide.Stars) -- namespace
local notation "T"=>town b
local notation "P"=>fun x=>D.C.wing (T x) D.rate
include D
lemma tiramisu : Geo G L (P) ∧ Geo G L (fun x:ℝ=> Visage.berth G (T x) k D.rate):=by
  let M x:= Duplex.town b x
  have hv : Geo G L (fun x=> ((M x).val:ℝ)):= by
    change Geo G L (fun x=> (↑(2*(Trio.tent b (radiusB x)+(0:Slide.Stars).val)) : ℝ)); simp only [Nat.cast_mul (α:=ℝ) 2, Nat.cast_add («R»:=ℝ) (Trio.tent b _), Nat.cast_ofNat]; exact (Geo.fixed 2).times ((Geo.basic (Trio.rows G L b).2.1).joins (Geo.fixed _))
  have he : Geo G L (fun x=> longitude D.rate (M x).val (royalty G)) := ((((Geo.fixed 4).times hv).times (Geo.fixed _)).times (Geo.fixed _)).joins ((Geo.fixed _).joins (((Geo.fixed 4).times hv).times (Geo.fixed _)))
  exact ⟨(Geo.fixed _).times (((Geo.fixed 1).joins ((Geo.fixed _).times he)).power k),(Geo.fixed _).times (((Geo.fixed 1).joins he).power _)⟩
lemma presold : Geo G L (fun x=> D.conjCost j (T x)) := ((((Geo.fixed 1).joins (D.tiramisu (L:=L) b).1).power _).times (Geo.fixed _))
lemma bulk_head (a:ℝ→ℝ)(ha: Geo G L a): ∃ V, Geo G L V ∧ ∀ᶠ t in atTop,
     ∀ β,Pressure.betaF G t L/2≤β→0<β→ 1 < a t → furl G L t < a t*gStep β → 1<V t∧ V t*gStep β ≤ 1 ∧ Ward.Duplex.Blurb D (town b t) (a t*gStep β) (V t*gStep β) (furl G L t):=by
   let W : ℝ→ℝ:= P; let U t:=(|W t|+2)*a t
   have hu :Geo G L U := ((D.tiramisu (L:=L) b).1.mean.joins (Geo.fixed 2)).times ha
   refine ⟨U,hu,?_⟩; filter_upwards [hu.uniform (show (0:ℝ)<1 by norm_num), ((D.tiramisu (L:=L) b).2.times ha).uniform D.C.charged] with t hp hx β h hii he hd
   have hg:=Fare.gS β hii|>.1; have hA:0<a t*gStep β:=mul_pos (zero_lt_one.trans he) hg
   have hs:a t≤U t:=le_mul_of_one_le_left (zero_lt_one.trans he|>.le) (by linarith only [abs_nonneg (W t)])
   refine ⟨lt_of_lt_of_le he hs,((mul_le_mul_of_nonneg_right (le_abs_self (U t)) hg.le).trans_lt (hp β h)).le, mul_le_mul_of_nonneg_right hs hg.le,hA.le,?_,?_⟩
   · rw [←mul_assoc]; exact (mul_le_mul_of_nonneg_right (le_abs_self _) hg.le).trans ((hx β h).le)
   change W t*(a t*gStep β)+ _ < (|W t|+2)*a t*gStep β; rw [mul_assoc (|W t|+2),add_mul]; have hW:=mul_le_mul_of_nonneg_right (le_abs_self (W t)) hA.le; linarith only [hA,hW,hd]
end Duplex
end YM.RGComparison01.Ward
-- old schedule output fee can lift retroactively
namespace YM.RGComparison01.Kraal.Stereo
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Tensor WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {K : KernelChoices} {C Z W' μ σ Λ σ' C' T₀ : ℝ} {q q' n k b p j j': ℕ} {v d W u : ℝ→ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o: Target.Order G W'} {J:Patch} {C₀ D t:ℝ}
    {A:Before G σ C J.J K (p+3)} {c c': Clip} {r f f' V T U X₁ X₂ Y : ℝ→ℝ}
lemma Board.remit (H : Board (σ':=σ') (C':=C') (d:=d) Q o J A c c' μ j j' q q' n k r f f' V C₀ D T U X₁ X₂ t) (he:X₂ t≤ Y t): Board (σ':=σ') (C':=C') (d:=d) Q o J A c c' μ j j' q q' n k r f f' V C₀ D T U X₁ Y t:=by
   intro a b S X F hh hK hf hX hh' hp Λ hF ρ hρ hC i Z hx h hw B B' m' β hT ht hv hQ v hp' D' r' hy E₀ e₀ hP hR
   have ht:=H a b S X F hh hK hf hX hh' hp Λ hF ρ hρ hC i Z hx h hw B B' m' β hT ht hv hQ v hp' hy E₀ e₀ hP hR
   refine ⟨ht.unmarked,fun J W hp ht'=>⟨(ht.marked J W hp ht').1, ((ht.marked J W hp ht').2).funding he (by unfold gStep; positivity) le_rfl⟩⟩
end YM.RGComparison01.Kraal.Stereo
-- make fee for w≥1
namespace YM.RGComparison01.Pledge
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Tensor WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {L:Side} {n j k q p w a b :ℕ}
lemma awards (h:ℝ)(hw:1≤ w) : |h| ≤ Archival.fee k j w |h| w:= by
   cases w with
   | zero=> omega
   | succ w =>
     rw [Archival.fee]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> mul_nonneg (by unfold Slate.levy; positivity) (Archival.produce (Archival.aside (abs_nonneg _) _) _))
lemma lined (P V D S R :ℝ→ℝ)(h:Geo G L P)(hp:Geo G L V)(hv:Geo G L D)(hx:Geo G L S)(hR:Geo G L R): ∃ T : ℝ→ℝ, Geo G L T ∧ ∀ x, R x ≤ T x ∧ (1≤w → S x ≤|Reels.tab k j w p q a (T x) (P x) (V x) (D x)|):= by
   let v x:= ritual_fee a k (P x) 0 (V x)
   let u x:=(k+1:ℕ)*(Reels.bunk w k p q a+1:ℕ)*D x
   let Y x:= |R x|+|S x|+|v x|+|u x|
   have hv': Geo G L v:= Kraal.for_ritual _ _ hp h
   have ht : Geo G L u := (Geo.fixed _).times hv
   refine ⟨Y,(((hR.mean.joins hx.mean).joins hv'.mean).joins ht.mean), fun x=> ⟨?_,fun hp=> ?_⟩⟩
   · unfold Y; linarith only [le_abs_self (R x),abs_nonneg (S x),abs_nonneg (v x),abs_nonneg (u x)]
   let A:=Archival.fee k j w |Y x| w; have hz:= (awards (k:=k) (j:=j) (Y x) hp)
   have hh : Y x ≤ A:= (le_abs_self _).trans hz
   apply le_trans _ (le_abs_self _); change _ ≤ A+v x + u x
   have hY:Y x= _:= (rfl : Y x = |R x|+|S x|+|v x|+|u x|)
   linarith only [hh,hY,neg_le_abs (v x),neg_le_abs (u x),le_abs_self (S x),abs_nonneg (R x)]
end YM.RGComparison01.Pledge
