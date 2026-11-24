import YM.FVA2.FallHistory
/-!
# FULL periodic torus stepwise formal coefficient ledger

Choose β_i = z_i / g_N² (step from i to i-1, indexing in DESCENT orientation); for use
 as specified, every z_i leading 1. Include z corrections on ALL costs via chip. The top
 physical input and the first top-down conditioning step have this same β. All link charts
 rescaled by g_N and use Coord clock unchanged through composition. Entire connected generator
 series (including off-coarse-field interaction force) retained. Exact & algebraic; no `PhysicalSum`
 identified with *different* endpoint convention without proof; this comparison implementation
 does not call `PhysicalSum ... false`. The supplementary D1 exported interface gives the
 companion analysis an option for reading FULL-period open coefficients (applying the same
 conditioning algorithm with/without inversion). **NOT** asserting bare full & quotient moment
 equality (would have to control different Wick contractions). Also not substituting masked
 re-evaluations or an offset empirical coupling. Later use with the ζ and geometric stamps to
 identify the seam data exactly. Limits used for the our formal-to-formal comparison are of
 the prescription on the inversion torus.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {c f n : Side}
variable (S:StepData c f)(T:Forest S.ratio)(d:Descent n f)(t:d.Tags)(b:S.Choices)
variable (Z:ChartRatio G)(z:ℕ→PowerSeries ℝ)(hz:LocalRatio Z)
local notation "Υ"=> partΥ G S T d
local notation "Eo"=> Coordinates G d
local notation "δo"=> gate G S T
local notation "Y"=> Future G S T
local notation "Kc"=> Pins G c

-- invoice before W. include factors along all path scope.
def chargeStep (Z:ChartRatio G)(b:S.Choices)(w:PowerSeries ℝ): Ticket (Future G S T × Pins G c):= boost (LinearMap.fst ℝ (Future G S T) (Pins G c)) ( tissue Z T.Free ) * chip w (tax S T b)
abbrev parentZ (z:ℕ→PowerSeries ℝ)(i:ℕ):= z (i+1)
lemma ready (Z:ChartRatio G)(hz:LocalRatio Z)(w:PowerSeries ℝ): incline (chargeStep S T Z b w):= pool (preserve_boost _ (awake hz)) (OpenSlots.restores ..)

abbrev bareF (G:Gauge)(n:Side)(x:Pins G n): ℝ:= _root_.YM.Wilson.energy (expLinks G _ x)

def supplyZ {c:Side}(d:Descent n c)(Z:ChartRatio G)(t:d.Tags) (z:ℕ→PowerSeries ℝ): Ticket ( SpaceF G d ):=
    match d with
    | .nil=> boost (LinearMap.snd ..) (chip (z 0) (bareF G n))
    | .push S T d' => boost (partΧ G S T d') (supplyZ d' Z t.2 (parentZ z)) * boost (partΥ G S T d') (chargeStep S T Z t.1 (z 1))
lemma clearZ {c:Side}(d:Descent n c)(Z:ChartRatio G)(t:d.Tags)(z:ℕ→PowerSeries ℝ)(hz: LocalRatio Z): incline (supplyZ d Z t z):= by induction d generalizing z with
    | nil=> rw [supplyZ]; exact preserve_boost _ (OpenSlots.restores ..)
    | push S T d ih=> rw [supplyZ]; exact pool ( preserve_boost _ ( ih .. ) ) ( preserve_boost _ ( ready S T _ Z hz _ )) -- ih needs generalized z

variable (h:Bid.Larger (G:=G) S)(H:d.Room G)
local notation "D"=> Descent.push S T d
local notation "Ψ"=> (jointV d t (G:=G))
local notation "τ"=> ( show (Descent.push S T d).Tags from (b,t))
local notation "Λ"=> jointV (Descent.push S T d) τ ( G:=G )
local notation "χ"=> CityHistory.fusion G S T d
local notation "ξ"=> partΧ G S T d
local notation "B"=> tax (G:=G) S T b
local notation "ωg"=> (expandGauge (K:=Pins G c) χ).toContinuousLinearEquiv.toContinuousLinearMap
local notation "Δg"=> (expandGauge (K:=Pins G c) χ).toLinearMap
local notation "fk"=> Quadratic.genesis 1 ( tax (G:=G) S T b )
local notation "Ω"=> innerV Λ χ
local notation "H₀"=> ( show ( Descent.push S T d ).Room G from ⟨h,H⟩ )
local notation "hq"=> gives (Descent.push S T d) τ H₀
local notation "hE"=> gives d t H
local notation "hY"=> useful S T d t b h H
local notation "hu"=> Tandem.stays Λ χ hq
local notation "Q"=> gateQ S T b (retained d t H)
abbrev city (G:Gauge){c:Side}(d:Descent n c):= tangent G d.Links
local notation "μ"=> city G D
local notation "μ0"=> city G d
local notation "ν"=> tangent G T.Free

local notation "W0"=> supplyZ d Z t (parentZ z)
local notation "U"=> (supplyZ D Z τ z)
local notation "W1"=> chargeStep S T Z b (z 1)
local notation "u0"=> Quadratic.uptake Ψ μ0 hE
local notation "u1"=> Quadratic.uptake Λ μ hq

def μLedger {c:Side}(d:Descent n c)(Z:ChartRatio G)(t:d.Tags)(H:d.Room G)(z:ℕ→PowerSeries ℝ): Ticket (Pins G c) := Quadratic.uptake (jointV (G:=G) d t) (city G d) (gives d t H) (supplyZ d Z t z)
lemma marketZ {c:Side}(d:Descent n c)(Z:ChartRatio G)(t:d.Tags)(H:d.Room G)(z:ℕ→PowerSeries ℝ) (hp:LocalRatio Z): incline ( μLedger d Z t H z ) := Quadratic.upright (jointV d t) (city G d) _ (clearZ d Z t z hp)
include h H
variable (A:Ticket ( SpaceF G d ))
local notation "upQ"=> Quadratic.uptake Q ν hY

-- Leib true continued path.
theorem parcel (v:Ticket (Y×Kc)) : (u1) (boost ξ A * boost Υ v )= ( upQ ) ( boost δo ( u0 A ) * v ):= by
    let X:= Quadratic.uptake Ω μ0 hu ( boost ( toward (E:=Eo) δo ) A * boost (LinearMap.snd ℝ Eo (Y×Kc)) v );
    have he : boost Δg (boost ξ A * boost Υ v)= boost ( toward (E:=Eo) δo ) A * boost (LinearMap.snd ℝ Eo (Y×Kc)) v := by
          apply Stack.into; intro x; rw [ caught,map_mul,caught,caught,map_mul,caught,caught, show ξ ( Δg x )= _ from part_s S T d x, show Υ ( Δg x )= _ from part_t S T d x ]; rfl
    have hh : X= boost δo ( u0 A ) * v:= by
          unfold X; have ha:= weigh Ψ hE fk δo μ0 A v; refine Eq.trans ?_ ha; congr 2; exact inherits_proof S T d t b h H
    rw [ Tandem.sew Λ χ hq μ ν μ0, he]; unfold X at hh; rw [hh]; congr 2; exact inherits_w S T d t b h H
local notation "ℱ"=> ( boost δo ( μLedger d Z t H (parentZ z) ) * W1 )

def fire (S:StepData c f)(T:Forest S.ratio)(b:S.Choices)(J:Ticket (Pins G f))(Z:ChartRatio G)(w:PowerSeries ℝ): Ticket (Future G S T × Pins G c):= boost (gate G S T) J * chargeStep S T Z b w
include hz in
lemma primeZ : incline ( fire S T b ( μLedger d Z t H (parentZ z) ) Z (z 1) ):= pool (preserve_boost _ (marketZ d Z t H (parentZ z) hz)) (ready S T _ _ hz (z 1))
theorem judgment : μLedger D Z τ H₀ z = (upQ) ( fire S T b ( μLedger d Z t H (parentZ z) ) Z (z 1) ):= by unfold μLedger; rw [supplyZ]; exact parcel S T d t b h H W0 W1
def premiere {c:Side}(d:Descent n c)(Z: ChartRatio G)(t:d.Tags)(H:d.Room G)(z:ℕ→PowerSeries ℝ) (A:Ticket ( SpaceF G d )) : Ticket (Pins G c):= Quadratic.fit (jointV (G:=G) d t) (city G d) (gives d t H) A (supplyZ d Z t z)
def solenoid (A:Ticket (Future G S T × Pins G c)): Ticket (Pins G c):= Quadratic.fit Q ν hY A ( fire S T b ( μLedger d Z t H (parentZ z) ) Z (z 1) )
-- proposition qlocal.Bud.At each call.B.Bind hp
omit h in
lemma share_part (Z:ChartRatio G)(hs:LocalRatio Z) : μLedger d Z t H z * premiere d Z t H z A=(u0) (supplyZ d Z t z * A):= Quadratic.fit_eq Ψ μ0 hE _ _ ( clearZ d Z t z hs )
include hz
-- call arbitrary dependency, retain v root dependence also.
lemma speaks (v:Ticket (Y×Kc)) : premiere ( D ) Z τ H₀ z (boost ξ A * boost Υ v) = solenoid S T d t b Z z h H (boost δo ( premiere d Z t H (parentZ z) A ) * v) := by
   let V:= μLedger d Z t H (parentZ z); let M:= premiere d Z t H (parentZ z) A; let W:= fire S T b V Z (z 1); let X:= boost δo V; let f:= W1
   let a:= boost ξ A * boost Υ v; have ht := judgment S T d t b Z z h H
   change premiere (D) Z τ H₀ z a = Quadratic.fit Q ν hY _ W; unfold premiere; apply (worth (marketZ _ Z τ H₀ z hz)).mul_left_cancel; change μLedger D Z τ H₀ z * _=μLedger D Z τ H₀ z * _
   rw [show μLedger D Z τ H₀ z * _= _ from Quadratic.fit_eq Λ μ hq a U (clearZ _ Z τ z hz) ]; rw [show μLedger D Z τ H₀ z = upQ W from ht, Quadratic.fit_eq Q ν hY _ W (primeZ S T d t b Z z hz h H)]
   have he : U*a=boost ξ ( W0* A ) * boost Υ (f*v):= by
        unfold a f; rw [supplyZ]; change (boost ξ W0* boost Υ W1)* _=(boost ξ (W0*A))* _; simp_rw [map_mul]; ring
   have hk : (u0) (W0*A)=V*M:= Eq.symm (share_part d t (parentZ z) H A Z hz)
   rw [he, parcel _ _ _ _ _ h H,hk, map_mul (boost δo) V M ]; apply congr_arg; change (_ * boost δo M) * ( f * v )=( X* f )* ( boost δo M * v ); unfold X; ring
lemma onlyPath : premiere ( D ) Z τ H₀ z (boost ξ A)= solenoid S T d t b Z z h H (boost δo (premiere d Z t H (parentZ z) A)):= by simpa only [map_one,mul_one] using speaks S T d t b Z z hz h H A 1
omit H h hz
-- top inserted amplitude on ambient.full E×K. Map on basis using projector points.
def placement {f:Side}(G:Gauge)(d:Descent n f): SpaceF G d→ₗ[ℝ] Pins G n :=
    match d with
    | .nil => LinearMap.snd ..
    | .push S T d=> (placement G d).comp (partΧ G S T d)

lemma placement_at (x: SpaceF G d) : d.fine (expLinks G _ x.2) (d.tablePath x.1)=expLinks G _ (placement G d x):= by
   induction d with
   | nil=> rfl
   | push S T d ih=>
     obtain ⟨⟨p,⟨y,z⟩⟩,rfl⟩:=( Tandem.expandGauge ( CityHistory.fusion G S T d ) ).surjective x; rw [ placement,LinearMap.comp_apply,hx_part,← ih,places]; change d.fine (T.drape (expLinks G _ y)) (d.tablePath p)= _; rw [ ← inserts S T y ] 

def skyread {f:Side}(Z:ChartRatio G)(d:Descent n f)(t:d.Tags)(H:d.Room G)(z:ℕ→PowerSeries ℝ)(A:Ticket (Pins G n)) := premiere d Z t H z (boost (placement G d) A)

include h H hz in
theorem atop (A:Ticket (Pins G n)) : skyread Z ( D ) τ H₀ z A= solenoid S T d t b Z z h H (boost δo ( skyread Z d t H (parentZ z) A )):= by
    unfold skyread; rw [placement]; rw [←onlyPath S T d t b Z z hz h H]; congr 1
-- nil valuation
section nil
variable (A:Ticket (Pins G n))(r:( Descent.nil (top:=n) ).Tags) -- parameter name
local notation "Γo"=> (Descent.nil (top:=n))
local notation "ε"=> Coordinates G Γo
local notation "ωδ"=> ( show (Γo).Room G from trivial )
local notation "Θ"=> jointV (Γo) r ( G:=G )
local notation "τ0"=> tangent G (Γo).Links
local notation "π0"=> gives (Γo) r ωδ
lemma zero_field (G:Gauge) (x:Coordinates G ( Descent.nil (top:=n) )): x=0:= funext (fun t=> Empty.elim (show Empty from t))
lemma frozen (x:Pins G n): (( retained (Γo) r ωδ ).flourish x)/2=jet (bareF G n) 2 x:= by
     change (Θ).flourish _/2=_; rw [progress]; let F:= consume (Γo) r (G:=G) 1; let C:= ContinuousLinearMap.snd ℝ ε (Pins G n)
     have ht:ContDiffAt ℝ ω (bareF G n) 0:= by
          let M:=ContinuousLinearMap.inr ℝ ε ( Pins G n ); rw [ show bareF G n=F ∘ M from funext (fun x=> (one_mul (bareF G n x)).symm) ]; exact ContDiffAt.comp (f:=M) _ ( thermal (Γo) r trivial _ ) M.contDiff.contDiffAt
     rw [show consume (Γo) r (G:=G) 1= bareF G n ∘ C from funext ( fun x=> one_mul _ ),GermLaplace.jet_pull C _ (ht.of_le le_top) ]; rfl
private lemma nil_uptake (A:Ticket (Pins G n)) : Quadratic.uptake Θ τ0 π0 (boost ( LinearMap.snd .. ) A )=A:= by
    apply PowerSeries.ext; intro i; unfold Quadratic.uptake throughPrice boost; apply Subtype.ext; funext x; simp only [ AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk,PowerSeries.coeff_map,LinearMap.toAddMonoidHom_coe ]; rw [Quadratic.integrateP_display];
    let z:ℝ:=(coeff i A).val x; let Qv:=Quadratic.RespectsPrice.inner π0; change Qv.average τ0 (fun _=> z)=z; unfold Law.average; simp_rw [Pi.mul_apply,integral_const_mul]; change z * ExactTower.capital Qv τ0 / ExactTower.capital Qv τ0=z; rw [mul_div_cancel_right₀ z (ExactTower.venture Qv τ0).ne']
lemma stock : μLedger (Γo) Z r ωδ z= chip (z 0) (bareF G n):= by unfold μLedger; rw [supplyZ]; exact nil_uptake _ _
include hz in
lemma invested : skyread Z (Γo) r ωδ z A=A:= by
    apply (worth (marketZ (Γo) Z r ωδ z hz)).mul_left_cancel; unfold skyread; rw [share_part _ _ _ _ _ Z hz, stock Z z]; rw [supplyZ,placement,← map_mul (boost _), nil_uptake ] -- needs parameters
end nil
end YM.FVA2.CityHistory
