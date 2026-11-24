import YM.FVA2.Gen.Midnight
/-!
# The nonlinear stencil highest Taylor symbol via smooth connections

This is a core part of connecting the **specific** stencils and MS rules. The statement
`morning` expresses the Taylor relation with a general smooth connection
and the actual *midpoint* phases in the physical mark data. `Near` concerns
orders in spacing (not in formal coupling!). See `Gen/Mender`, `Gen/Midnight` for the step
that lets us replace Taylor arcs via higher order corrections to the connection.
Use `Gen/Recipe`, `Gen/Dome` for taking radial jets (the formal algebra in the
specified `Jrad` convention, not treating classical physics assumptions as axioms
of this perturbative calculation).
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision Source Wilson Drops Work G05 Bid
open Press XSpace
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge}{A: Sky G}{J:Labels.Jet G}{H:Hol G}{x:E4}{i:Axis}{k d n:ℕ}(S:XSpace.Survey G H d){Z:Arc ℝ G}{Q:Vehicle ℝ G}
local notation "U"=> G.mat
local notation "κ"=> Fin (d-1)
-- cost drift along tilt only projected heights & all root Mark polynomial if desired.
abbrev Chest (G:Gauge)(j:ℕ) := Module.Dual ℝ ( Labels.Taylor G j )
abbrev truth (G:Gauge) (d:ℕ) (i:Fin (d-1)) (f:Chest G i.val): Snap G d →L[ℝ] ℝ:= LinearMap.toContinuousLinearMap ( f.comp ( LinearMap.proj i ) )
local notation "SC"=> Survey
abbrev minZ {i:ℕ}(f:Chest G i)(J:Jet G)(t:ℝ):= t^(i+2) • ( f (J i) )
variable {S}
lemma dyn {F:ℝ×ℝ→ E}(k:ℕ){A:E}(he:∀ x:ℝ,ContDiffAt ℝ ∞ F (x,0))(hf:∀ x:ℝ,∃ v:E,Near k (fun t=>F (x,t)) (fun t:ℝ=> t^k • v))(h:Near k (fun t=> F (0,t)) (fun t:ℝ=> t^k • A)): Near k (fun t=> F (t,t)) ( fun t:ℝ=> t^k • A ):=by
    let Y(s:ℝ):= (( k.factorial:ℝ ))⁻¹ • iteratedDeriv k (fun t:ℝ=> F (s,t)) 0; have hY:ContDiff ℝ ∞ Y:= ( priced he k ).const_smul _
    have hh(x:ℝ)(v:E)(hv:Near k (fun t=>F (x,t)) ( fun t:ℝ=> t^k • v )): Y x=v:=by unfold Y; rw [ hv k le_rfl,lift_symbol,if_pos rfl, inv_smul_smul₀ (by positivity: (k.factorial:ℝ)≠0) ]
    let g(t:ℝ×ℝ):= t.2^k • Y t.1; have hG:ContDiff ℝ ∞ g:= ( contDiff_snd.pow _ ).smul ( hY.comp contDiff_fst ); have hd(x:ℝ): Near k (fun t=> F (x,t)) (fun t=> g (x,t)):= by obtain ⟨u,hv⟩:= hf x; dsimp only [g]; rw [ hh x u hv ]; exact hv
    let p(t:ℝ):= (t,t); refine ( ( parameter hd he (fun x=> hG.contDiffAt) (0:ℝ) ).along ( p:=p ) rfl (contDiffAt_id.prodMk contDiffAt_id) (he 0) hG.contDiffAt ).across ?_; change Near k (fun t:ℝ=> t^k • Y t ) _; rw [ ← hh 0 A h ]; exact onRail k hY.contDiffAt
private lemma steadC (J:Labels.Jet G) (d:ℕ): ContDiff ℝ ∞ (fun t:ℝ=> trunk d ( scaleJet J t )):= by
    have h {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](k:ℕ)(f:F): ContDiff ℝ ∞ (fun t:ℝ=> t^k • f):=( contDiff_id.pow _ ).smul contDiff_const
    exact contDiff_pi.mpr (fun k=> h (k.val+2) (J k.val))
private lemma flown (h:Leads Q Z)(hp:Flo Z){x':ℝ}(hA:Radials ( Z x' ) J)(S:XSpace.Survey G H d)(j:κ)(v:Chest G j.val): Near (j.val+2) ( truth G d j v ∘ S.reading ∘ ( bookend ( earth Q x') ) ) (minZ v J):=by
    let p:= bookend ( earth Q x'); obtain he:= rung S (h.air x') (hp.road x') hA
    have hc:ContDiffAt ℝ ∞ ( S.reading ∘ p ) 0:= cover_c S ( air_cover ( h.air x' ) ( hp.road x' ) ); let L:=truth G d j v
    have ht:= Near.vcomp (ψ:=L) he hc ( steadC J d|>.contDiffAt ) L.contDiff.contDiffAt
    let p:ℝ→ℝ:= fun x=> v (J _); rw [show minZ v J=L ∘ (fun t:ℝ=> trunk d ( scaleJet J t )) from funext fun t=> ( map_smul v (t^(j.val+2)) ( J _ ) ).symm ]; exact ht.low (by have hx:= j.isLt; omega)
lemma Leads.drift (h:Leads Q Z)(hp:Flo Z)(S:XSpace.Survey G H d)(hA: Radials ( Z 0 ) J)(j:κ)(v:Chest G j.val): Near (j.val+2) (fun t:ℝ=> v ( S.reading (convoy Q t) j ) ) ( minZ v J ):=by
    let f(t:ℝ×ℝ):=v ( S.reading ( bookend ( earth Q t.1 ) t.2 ) j )
    apply dyn (F:=f) _ (A:=v ( J j.val ))
    · intro x; let L:= truth G d j v; let g(t:ℝ×ℝ):=bookend (earth Q t.1) t.2; exact L.contDiff.contDiffAt.comp (f:= S.reading ∘ g) (x,0) (cover_c S ( readyQ h hp x ))
    · intro x; obtain ⟨J,hv⟩:= origin (hp.road x); exact ⟨ v (J j.val), flown h hp hv S j v ⟩
    exact flown h hp hA S j v
/-- *Classical and on the midpoint indicators*: real jets on unrenormalized fields, not the
actual expectation. Conclusion does not use any paths depending on the smooth test spacing family;
instead the conclusion is directly with log-midpoint samples from `A`. -/
lemma morning (h:Fluid A) (S:XSpace.Survey G H d) (he: Radials A J) (j:κ) (v:Chest G j.val) :
    Near (j.val+2) (fun t:ℝ=> v ( S.reading (phaseQ A t) j )) ( minZ v J ) := by
    obtain ⟨Z,Q,hp,hz,h0,B⟩:= adjust A h d
    let p:= convoy Q; let α:= truth G d j v; obtain ht:= convoy_f S h hp hz B; apply Near.across _ (p:=α ∘ ( S.reading ∘ phaseQ A )) ( hp.drift hz S ( h0.symm ▸ he ) j v ); let D(t:ℝ×ℝ) := bookend ( earth Q t.1 ) t.2; have hD:ContDiffAt ℝ ∞ ( S.reading ∘ ( convoy Q ) ) 0:= ( cover_c S ( readyQ hp hz 0 ) ).comp 0 (f:=fun t:ℝ=>(t,t)) ( contDiffAt_id.prodMk contDiffAt_id ); exact ( ht.vcomp ( cover_c S ( day_C h ) ) hD α.contDiff.contDiffAt ).low (by have h:= j.isLt; omega)
-- sensed through raw angular lift.
abbrev reading (S:XSpace.Survey G H d)(i:κ)(x:tilt S):= S.reading ( Press.pad S x ) i -- name conflict
abbrev campaigning (A:Sky G)(S:XSpace.Survey G H d) (t:ℝ): tilt S:= fun i=> logQuad A t i.val
lemma calls (A: Sky G) (S:XSpace.Survey G H d) (t:ℝ): S.reading (phaseQ A t)=S.recover (Press.lamp S (campaigning A S t)):=congrArg S.recover (reception S _ ( t:=phaseQ A t ) (fun _=> rfl))
end YM.FVA2.Gen
