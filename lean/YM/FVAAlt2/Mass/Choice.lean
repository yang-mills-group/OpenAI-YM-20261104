import YM.FVAAlt2.Mass.Output
import YM.FormalOPE.RG10.Boardwalk.Stagecraft
/-!
# Agreement with the logarithmic Rails prescription (whenever using flow)
The stronger inputs `Street` incl optional flow are not assumed in supplying
MassCost.equality. Here we prove agreement with the generator prescription, whenever also
 supplied as in the manuscript (uses standard continuity of individual normalized scaling relations).
 New substitute for Part lemma `Passe.recovered` based on engineering-power invariance
rather than the shared dynamics.In particular MS comparison imposes no β equations. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Mass
open Function Finset Filter MeasureTheory Topology Set Metric
open Labels Precision Extra.FD Maxwell Extraction FormalOPE FormalOPE.RG10 RG10.Position.Grade
open PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Position.Triangle RG10.Position RG10.Gazebo RG10.Carryon RG10.InversionTop
open MS MS.Koszul MS.Menus MS.Book MS.Local.Physical MS.Land MS.FVA.Currency
open PowerSeries (C coeff constantCoeff)
open Home Home.Report Matrix Home.Profiles Convert Next.UVStress
open Real
open scoped Topology BigOperators PowerSeries ContDiff Classical Matrix
variable {G:Gauge}{F:Frames G}{d k m n:ℕ}
local notation:max "V_" d:max => RG10.Position.Deck F d
local notation "V"=> RG10.Position.Deck F d
local notation "ζ"=> Deck.price F d
variable {P:Plan F}{W:Drivers}(R:Rails F) (Y: Patience P W)
lemma roundF {x:Test m}(t:ℝ) : scaleT (-t) (scaleT t x)=x:=by
 have ht:= Arrangements.dilations (n:=m) t t x; change scaleT (-t) (scaleT t x)=_; refine ht.trans ?_; rw [ sub_self ]; ext1 i; change (( ↑(( exp 0^(4*m))⁻¹) :ℂ) * x ((exp 0)⁻¹ • i) )=_; rw [ exp_zero,one_pow, inv_one, one_smul, Complex.ofReal_one, one_mul ]
lemma dialysis {I:Type*}(b:Datum I)(s:ℝ): Position.dial s (nearD s b)=b:= by
 obtain ⟨⟨m,f⟩,p⟩:=b; change (⟨⟨m,scaleT (-s) (scaleT s f)⟩,p⟩:Datum I)= _; -- heq
 exact congr_arg (fun f:Test m=> (⟨⟨m,f⟩,p⟩:Datum I)) (roundF s)
local notation "H"=> R.route d
local notation "Φ"=> R.flow
-- budgets on literal Psi.Tensor: continuity group, locally any.
def Fluid (R:Position.Grade.Rails F):Prop:= (∀ d, Continuous (fun s:ℝ=> coeff d (R.flow.psi s))) ∧ ∀ d n (i j: RG10.Position.Deck F d), Continuous (fun s:ℝ=> coeff n ( (R.route d).train s i j ))
set_option quotPrecheck false
local notation "C1"=> R.adjust Y d
private lemma vessel (s:ℝ)(i j:V): C ( moving ( ζ i ) s ) * ( H ).drive s i j=( H ).lift s i j:= by rw [ Passe.lift_apply, moving ]; rw [ ←Real.exp_nat_mul, mul_comm (↑(ζ i):ℝ) ] -- args mismatch
lemma law_at (h:Street Y R) (s:ℝ)(v:Datum V) : (Φ).warp s ( (C1) ( nearD s v ))=mix (C1) ((H).drive s) v:= by
 obtain he:= Rails.relocation h s (a:=d); obtain hp:= congr_fun he (nearD s v); obtain ⟨⟨m,f⟩,p⟩:=v; apply hp.trans; unfold mix; change (∑ i:Fin m→V,(C1) ( Position.dial s ( nearD s (⟨⟨m,f⟩,i⟩:Datum V) ) ) *_) = _; simp_rw [ dialysis ]
-- derive Polys.Genuine ahead log.Time
variable (h:Street Y R) (hg:Fluid R)
include h hg
lemma steam (v:Datum V) : ∀ n:ℕ, Polys (fun s:ℝ=>coeff n ( C ( moving ( tallyW ζ v ) s )* (C1) ( nearD s v ) )) :=by
 intro n
 have hz (s:ℝ): C ( moving (tallyW ζ v) s )*( C1 ) ( nearD s v )=(Φ).warp (-s) (mix (C1) ((H).lift s) v):=by
   have hh (i:ℝ)(f:fps): (Φ).warp (-i) ( (Φ).warp i f)=f:=by simpa only [neg_neg] using R.ok.neutral (-i) f
   nth_rw 1 [ ← hh s ( C _*_ ) ]; rw [map_mul ( (Φ).warp s ), Flow.at_const, law_at R Y h ]; refine congr_arg ((Φ).warp (-s)) ?_
   unfold mix; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [ mul_left_comm ]; congr 1; simp_rw [ ← vessel ]; rw [ Finset.prod_mul_distrib, ← map_prod C ]; simp_rw [moving,Finset.prod_pow_eq_pow_sum]
 have he(i:ℕ): Polys (fun s:ℝ=> coeff i (mix (C1) ((H).lift (-s)) v)):=by
   let L(k:ℕ):= fun i:Fin v.1.n→V=> fun s:ℝ=> (C1) (⟨v.1,i⟩:Datum V) * ∏ t:Fin v.1.n,( H ).lift (-s) (v.2 t) (i t)
   let Lf(f:ℝ→fps):=∀ k,Polys (fun s=> coeff k (f s)); have h1(j:fps):Lf (fun _=>j):=fun i=>Polys.const _; have hu(f g:ℝ→fps)(hf:Lf f)(hh: Lf g): Lf (f*g):= by intro n; simp_rw [Pi.mul_apply,PowerSeries.coeff_mul]; apply Polys.sum _ _ (fun i _=> Polys.muls ( hf i.1 ) ( hh i.2 )) -- check<br>
   have hp(t: Fin v.1.n→V)(s:Finset (Fin v.1.n)): Lf (fun j:ℝ=>∏ x∈s,( H ).lift (-j) ( v.2 x ) (t x)):= by
      induction s using Finset.induction_on with
      | empty=> simpa only [Finset.prod_empty] using h1 1
      | insert a s hS ih=> simp_rw [Finset.prod_insert hS]; exact hu (fun s=>( H ).lift (-s) (v.2 a) (t a)) _ (fun i=> ( Passe.uniform_lift ( H ) (hg.2 d) i (v.2 a) (t a) ).stretch ) ih
   unfold mix; simp_rw [ map_sum ]; exact Polys.sum _ _ (fun t _=> hu _ _ (h1 _) (hp t _) i)
 have ht:= Cycle.fares (f:=fun s=> mix (C1) ((H).lift (-s)) v) R.ok hg.1 (n:=n) (fun i _=> he i ); obtain hs:=ht.stretch; simp only [neg_neg] at hs; simp_rw [hz]; exact hs
lemma rail_form : Framed P Y ( R.book ) := by
 refine ⟨ fun d=> ⟨ ⟨ (R.route d).first_base, Boardwalk.Stagecraft.mainBook R ⟩, (R.route d).booked.2.1, fun v i=>?_⟩, fun {_ _} h=> Rails.scaled_across R h⟩
 obtain hv:= steam R Y h hg v i; simp_rw [ PowerSeries.coeff_C_mul ] at hv; exact hv
end YM.FVAAlt2.Mass
