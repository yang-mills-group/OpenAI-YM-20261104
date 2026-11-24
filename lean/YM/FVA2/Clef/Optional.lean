import YM.FVA2.O.Canon.Give
import YM.FVA2.Clef.Winds
/-!
 # Any final within-grade near-free rotation adjustment, formal-to-formal

 No additional rotations needed for this task (keep `Clef.Winds` choice, it
 already preserves reality, unit, signs, filtration, grades). Here cover
 reexpression in case analytic comparison requires another final **within-grade**
 change additionally. No regularity assumption beyond formal & genuine grade
 correctness. E.g. may have a *linear* term in that change, while STILL recovering
 the same `check b` order-two guarantee. Not claiming any special stress alignment
 chosen; any hypothesis specific to that use belongs elsewhere.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clef
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta Generator.Der Generator.Drive
variable {G:Gauge}{d n i j:ℕ}
namespace Optional
open O O.Score O.Enh O.Bind O.Project O.Read
open scoped Matrix
-- degreewise extension
variable {Y: Initialize G}{V:Normalize.Store G}{K:Rose.Pick V}
variable (T: MS_Data G (Position.OpenAxis.Plot ( Press.portDeck G )))
variable (h:G.Simple) (ν:ℝ) {M:Prescription (Press.portDeck G)}
local notation "X₀" => Measure.outlook Y K
local notation "X₁" => Scale.Equator.wave ν T
local notation "γ" => GroupS.ψ K T ν
local notation "B" => GroupS.gaugeN Y K T ν
local notation "E₀" => GroupS.Ψ K T ν
local notation "T₀" => GroupS.gaugeM Y K T ν
local notation "Z₀" => Scale.Measure.Z Y K ν T
local notation "p" => Scale.Measure.f K ν T
variable (H:System.Contract Y K T M)
variable (A:Frames G)(hA:Civil A)
local notation "T'"=> rendition X₀ A
local notation "A'"=> breeze A γ B
local notation "u"=> ( Z₀ * A )
include H hA ν
omit hA in
lemma operator ( d:ℕ ): actMark (u d) ( couple p (wave ν T d) )= T' d:= by rw [rendition, ← H.series ν,Facets.acts]; rfl
lemma independence (A₁: Frames G)(q:Cn)(hq:Scale.Tangent q)(he:∀ i,Base (A₁ i))(hp:∀ i,actMark (A₁ i) (couple q (wave ν T i))=T' i): q=p ∧ A₁=u:= by
    apply ( H.scales ν|>.minimal.whole ) _ _ _ _ hq ( H.cpl ν ) he _ (fun i=> ( hp i ).trans ( operator T ν H A i ).symm ); intro i; exact ( H.joint ν i ).1.mul ( hA.hue i )
lemma color : Civil u:= ⟨ fun i=>( H.joint ν i ).1.mul (hA.hue i),fun i=> (H.joint ν i).1.befits (H.joint ν i).2.1 (hA.hue i) ( hA.dear i ),fun h=> (( H.sees h ν ).1).mul ( hA.growth h ) ⟩
lemma usual : Regular T':= marks (( Canon.after_W H ν ).dimensions) hA
lemma rendered : ExchangeA p ( seats u ) ( install X₁ ) = install T':= by
    rw [ ExchangeA, tune_live ( H.cpl ν|>.start ), unveil ( tune_reg ( regular_wave ν T ) ) ( color _ _ H A hA ), show Mark u (TuneQ p X₁)=T' from funext ( operator T ν H A ) ]
lemma plays : Ground T':= fun i=> step_mark _ _ ( hA.hue _ ) ( Canon.after_W H ν |>.wardRank i )
omit H in
lemma differs (t:ℝ): B t d * stepV (γ t) ( A d )=A d * A' t d:= by rw [ ← freeze (fun i => hA.hue i),old_g _ _ ( hA.dear _ ) ]
include h
lemma Column : Law T' γ A':= by
    have hM:=Canon.after_W H ν |>.scope; -- mass grade
    apply Precise.lawfully (Y:=Y) T M h H.toMission.born.Taylor _ _ _ (growth hM.toTouched hA.hue ( fun i j H=> hA.growth H ) ) ( plays T ν H A hA ) hM.smooth ( fun i=> Scale.Equator.powers_m _ _ ( hM.meets _ _ _ i ) ( hA.dear i ) ); intro t d; unfold breeze; rw [ old_g _ _ ( hA.dear d ) ]; exact Base.befits ((hA.hue d).rewind.mul (hM.paid t d)) (( hA.hue d ).rewind.befits (( hA.hue _ ).matter ( hA.dear _ )) ( hM.paid t d ) ( hM.ready t d )) ((hA.hue d).switch ( hM.led t|>.real )) ( Base.paid_sub _ ( hA.dear d ) )
-- slope. use same private algebra facts as in Qgau.
omit T ν h H hA in
private lemma birth_r (q:Cn)(hp:Scale.Tangent q)(X:Guard G d): coeff 1 (stepV q X)=coeff 1 X:= by
    rw [stepV,coeff_mk,rules, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ, Finset.sum_range_one]; simp [cut,hp.lead]
omit T ν h H hA in
private lemma matter_r (C G:Guard G d)(r:Base C)(q: Base G): coeff 1 (C*G) =coeff 1 C+coeff 1 G:= by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f:= fun i j=> coeff i C * coeff j G), Finset.sum_range_succ, Finset.sum_range_one,r.zero,Nat.sub_self,Nat.sub_zero,q.zero]; simp only [ one_mul,mul_one ]; exact add_comm ..
lemma first_b (t:ℝ): coeff 1 (A' t d)=0:= by
    obtain hL:= Column T h ν H A hA; obtain hm:=( H.scales ν ).check
    obtain hh:= congr_arg (coeff 1) ( differs (K:=K) T ν A hA (d:=d) t ); have H0:=H.toMission.toSchemeV.born; rw [ matter_r ( B t d ) _ ( hm.paid t _ ) ((hA.hue _).switch ( hL.led t|>.real)), Generator.Q.lifted ν Y K T M t h H0.Taylor H0.still H0.base, birth_r _ ( hL.led t ), zero_add, matter_r _ _ ( hA.hue _ ) ( hL.paid t _ ) ] at hh; have hz {V : Type} [AddCommGroup V] (a v:V)(h:a=a+v) : v=0:= add_eq_left.mp h.symm; exact hz (coeff 1 (A d)) _ hh
lemma price : Slopes T' γ A' ( Generator.Drive.engraving A' ):= by have hh:= ( Generator.Drive.clocks_run Y K T M h H ν ).1; exact Slopes.ingrain ( Column T h ν H A hA ) ( fun i=> first_b T h ν H A hA ) ( fun _ HK => hh.startg HK ) hh.beta0
omit h in
lemma interconnected (t:ℝ)(d:ℕ): stepV p (T₀ t d) * stepV (γ t) (u d) = u d * A' t d:= by
    rw [ Pi.mul_apply, Scale.Frame.step_mul (Z₀ d) _ _ (( H.scales ν ).check.led t |>.start ), ← mul_assoc, ( H.scales ν ).fields, mul_assoc, differs (K:=K) T ν A hA ]; rw [ ← mul_assoc ]
lemma in_fields : Canon.Physical T' γ A':= by
    obtain hu:= Canon.before_M H ν
    have ht:= ( H.cpl ν ).start; have hr:= usual (Y:=Y) T ν H A hA; have hc:= color T ν H A hA; have hz:= rendered T ν H A hA
    apply Canon.Physical.shine ( Column T h ν H A hA ) ( hz ▸ observing ( T:=seats u ) ht hu.awake ) ( plays T ν H A hA ) hr; intro n i; rw [ ← hz ]; exact ⟨ _, funds_good ht ( spin_k hc ) hu.far ⟩
lemma transferred {n:ℕ}(i:Scan G n) : Canon.LogPricing T' i= holding p ( seats u ) ( seats ( replay u ) ) ( Canon.LogPricing X₁ ) i:= by
    apply Canon.Physical.unique ( in_fields T h ν H A hA ) i; rw [ ← rendered T ν H A hA ]; exact paid_w ( H.cpl ν |>.start ) ( spin_k ( color T ν H A hA ) ) ( Canon.before_M H ν|>.works )
lemma assists { n:ℕ } (r:ℝ)(i:Scan G n): Canon.Gift_shape ( seats u ) p i ( fun v=> Canon.OPECoefficients X₁ v r ) ( Canon.OPECoefficients T' i r ):= by
    intro x; apply Gift.total ( H.cpl ν |>.start ); rw [ transferred T h ν H A hA ]; apply O.Project.rate ( spin_k ( color T ν H A hA ) )
end Optional
end YM.FVA2.Clef
