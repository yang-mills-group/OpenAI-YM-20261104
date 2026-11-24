import YM.FVAAlt2.Moving.Sound
/-!
# Exact finite regulator before independent Peal normalization
See Landing lemma for moving Track pipelines. Same orientation by choosing primitive glyphs from the same $off$ as top story (and its Owner frames), don't substitute a narrative about restoring the bake.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Moving.Perot
open Set Function Filter MeasureTheory Real Topology
open Lattice Precision RG PhysicalNext.Repeat.Legato Epoch Calibration Rocket Oracle Circuit Lodge Ledger Ledger.Sky Taping Period.Field Sound CalendarT Pegs
open MS MS.Land MS.Menus MS.Dial MS.Vista MS.Fleet MS.Orbit MS.Tone MS.Tide
open Integration RunFormalChain Pipeline Pipeline.See Figure
open YM.FVAAlt2 YM.FVAAlt2.Home.Profiles YM.FVAAlt2.Home YM.FVAAlt2.Home.Report
open Finset Metric Labels Extra.FD Maxwell Source Extraction FormalOPE PertExtension PertExtension.LatticePT PertExtension.Position FormalOPE.RG10.InversionTop
open RG10.Position (Plan Spur Loft)
open PowerSeries (C coeff constantCoeff)
open scoped Topology ENNReal NNReal BigOperators PowerSeries Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X:Type}{d r:ℕ}{F:Frames G}{H:Source.Hol G} (R:Lobby.Registry F H) (B:Lodge.Track X)(x:X)
local notation "PS"=> PowerSeries ℂ
local notation "ϵ"=> Sound.Alone B x
variable (P:Plan F) {D:MS.Local.Physical.Deck G}(T: Exhibit B x F)(Γ:MS.Land.Prescription D) (μ:ℝ)
abbrev Period (v:Fin r→ MS.Rake.Label D)(φ:Points r→ℝ):= Pegs.compilation B x (fun u=> Sound.Formal.dated Γ (μ-B.Θ x) R v ( Alone B x ) (T _ u)) φ
noncomputable def report (u:Home.Datum (Glyph D d)): PS:= Perot.Period R B x T Γ μ (Lobby.owner∘ u.snd) (Home.dim_report u)
lemma lengths : Sound.Alone B x=epsilon ( B.L x ) ( B.batch x ):= by rw [← theta_sc]; rfl
lemma shiftL : B.Θ x= Home.Profiles.Θ (B.L x) (B.batch x) := rfl
lemma inward (p:Points r→ℝ)(T:Pegs.Motor B r x→PowerSeries ℂ) : Lobby.redo Γ.team (μ-B.Θ x) ( Pegs.compilation B x T p )= Pegs.compilation B x ( Lobby.redo Γ.team ( μ-B.Θ x ) ∘ T ) p:= by unfold Pegs.compilation; rw [map_sum]; simp only [Function.comp_apply,← PowerSeries.smul_eq_C_mul,map_smul]
section lift
variable (D' : Fin r→ MS.Rake.Label D)(y:ℝ)
set_option quotPrecheck false
local notation:max "I" i:max=> MS.Menus.Glyph D ((D' i).h)
abbrev Fund (ε:ℝ)(U:Sound.Formal.Episode (Fin r) F)(v:Fin r→ MS.Rake.Label D): PS:= C ( (↑ε:ℂ)⁻¹ ^ Lobby.wt v ) * Sound.Formal.baseV R v U
lemma glyphFact (i:Motor B r x) (v:(j:Fin r)→ (I j)) :
    let V(j:Fin r):= Lobby.owner (v j)
    C ( (↑ϵ:ℂ)⁻¹ ^ Lobby.wt D' ) * (( ∏ j,Billing.bore D' Γ y j (v j))*Lobby.redo Γ.team y (Sound.Formal.baseV R V (T _ i)))=(∏ j,Lobby.changePrice Γ y D' ϵ j (v j)) * Lobby.redo Γ.team y (Fund R (ϵ) (T _ i) V):= by
 intro W; rw [Fund, show C ( (↑ϵ:ℂ)⁻¹ ^ Lobby.wt W ) * _=(( (↑ϵ:ℂ)⁻¹ ^ Lobby.wt W ) • Sound.Formal.baseV R W (T _ i)) from ( PowerSeries.smul_eq_C_mul .. ).symm, map_smul,PowerSeries.smul_eq_C_mul]
 unfold Lobby.changePrice; rw [Finset.prod_mul_distrib]; let u:ℂ:=↑ϵ
 have he:u≠0:=by unfold u; exact_mod_cast (ne_of_gt (exp_pos _ : 0 < (ϵ)))
 let c:=PowerSeries.C (R:=ℂ); let f(j:Fin r):ℂ:= u^(((W j).h:ℤ)-(D' j).h)
 have H(d:Fin r→ Rake.Label D): c (u⁻¹ ^ Lobby.wt d)=∏ i:Fin r,c (u⁻¹ ^ (d i).h):=by rw [← map_prod c,Finset.prod_pow_eq_pow_sum ]
 have ht : (∏ i:Fin r,c (f i))*c (u⁻¹ ^ Lobby.wt W)= c (u⁻¹ ^ Lobby.wt D'):=by rw [H W,H D',← Finset.prod_mul_distrib]; apply prod_congr rfl; intro i _; rw [← map_mul]; unfold f; rw [zpow_sub₀ he, zpow_natCast,zpow_natCast, inv_pow,inv_pow]; congr 1; field_simp
 change c (u⁻¹^_)*_=( (∏ i:Fin r,c (f i))* _ )*( c _*_); rw [← ht]; ring
lemma paid (φ:Points r→ℝ) : Period R B x T Γ μ D' φ= ∑ v:(j:Fin r)→ I j,(∏ j,Lobby.changePrice Γ (μ-B.Θ x) D' ϵ j (v j)) * Lobby.redo Γ.team (μ-B.Θ x) ( Pegs.compilation B x (fun i=> Perot.Fund R (ϵ) (T _ i) (fun j=> Lobby.owner (v j))) φ ):=by
 simp_rw [inward B x Γ μ]; unfold Perot.Period Pegs.compilation Sound.Formal.dated Sound.Formal.songbook; -- don't simplify under sums? appear with b.Market. need commute
 simp_rw [Function.comp_apply, Finset.mul_sum]; rw [Finset.sum_comm]; apply sum_congr rfl; intro v _; apply sum_congr rfl; intro i _; rw [ ← mul_left_comm ( C (↑( earn B x φ i ):ℂ)) ]; exact congr_arg _ (glyphFact R B x T Γ D' (μ-B.Θ x) i v)
end lift
variable (h:∀ n b i v, RSpec (T n b i v))
lemma connect : Perot.report R B x T Γ μ (d:=d)= mix ( Lobby.redo Γ.team (μ-B.Θ x) ∘ Story R B x T ) (Home.aboard Γ ϵ (μ-B.Θ x) d):=by
    funext p; rcases p with ⟨φ,u⟩; let W (i:Fin φ.n):= Lobby.owner (u i); let S(i:Fin φ.n):=Glyph D ( W i ).h; let tx(i:Fin φ.n)(j:S i): Glyph D d:= up (Home.high (u i)) j; symm; rw [ monoread (p:=φ) u _ _ tx (fun i=> up_inj _) ?hp ]; swap
    · intro i j hu; unfold aboard; rw [Matrix.of_apply,oilPoint]; exact sum_eq_zero fun k _=> if_neg (fun h=> hu ⟨k,h⟩ )
    unfold Perot.report; rw [ Perot.paid ]; refine sum_congr rfl fun i _=>?_ ; rw [ mul_comm ]; exact congr_arg₂ (· * ·) (Finset.prod_congr rfl fun j _=> Home.onOil ..) rfl
include h
lemma evident (q:Home.Datum (Glyph D d)) : RSpec ( Perot.report R B x T Γ μ q ):=by
 rw [connect]; refine RSpec.finSum _ (fun _ _=> RSpec.mul ( specRedo _ _ (realstory R B x T h _) ) ?_ ); apply RSpec.finProd; intro k hk; rw [lengths,shiftL]; exact realOil ..
omit h
variable {P μ}{Ω:Prescription (Home.seats P.liftOff P.certified)}
noncomputable def turned {F:Frames G} (P:Plan F)(μ:ℝ)(Γ:MS.Land.Prescription (Home.seats P.liftOff P.certified))(T: Exhibit B x F)(d:ℕ):Home.Datum (RG10.Position.Deck F d) → PowerSeries ℝ:= PertExtension.Position.insert _ _ ((PowerSeries.subst ( revise Γ.team (μ-B.Θ x) )) ∘ (takeReal∘ Perot.Raw B x T P d)) ( Convert.fares P Γ μ (B.L x) (B.batch x) d )
include h
lemma exact_economic (μ) : Perot.turned B x P μ Ω T d= mix (takeReal∘ report (nativeR P) B x T Ω μ) ((dout F (Home.seats P.liftOff P.certified) d).map C):=by
 let Y:=P.begins; let S:=seats P.liftOff P.certified; let K:=B.batch x; let L:=B.L x
 let b:=Perot.Raw B x T P d; let ρ:=Lobby.redo Ω.team (μ-B.Θ x)
 suffices he : into ∘ turned B x P μ Ω T d= into ∘ mix (takeReal ∘ report (nativeR P) B x T Ω μ) ((dout F S d).map C) by exact funext fun v=> rein (congr_fun he v)
 have hp(i:Home.Datum (RG10.Position.Deck F d)): b i= into (takeReal (b i)):= Eq.symm (realraw B x T h P i)
 unfold Perot.turned; rw [mixSame,mixPap,mixPap,show into ∘ (takeReal∘ report (nativeR P) B x T Ω μ (d:=d)) = _ from funext ( fun i=> Perot.evident (nativeR P) B x T Ω μ h i ), ← θout F, Perot.connect, shiftL ]; rw [Convert.fares,frame_board,lengths,stateMean,Home.redoes,mix2,mix2, Matrix.mul_assoc]; congr! 1; funext i; unfold Function.comp; -- primary b θ
 apply Eq.symm; conv_lhs=> rw [ show Raw B x T P d i= _ from hp i ]; exact tidy ..
end YM.RegulatorIR.FVAAlt2.Moving.Perot
