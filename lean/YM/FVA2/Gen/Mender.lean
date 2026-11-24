import YM.FVA2.Gen.Lanes
/-!
# Deterministic jet adjustment by one spacing power

From midpoint phase to the holonomy prescription requires a higher-order repair,
exact through any fixed order on a genuine connection family. `fixZ` constructs the
repair arc, `step_R` compares in log coordinates. Classical connection argument,
not a statement about moment convergence in the UV cutoff limit!
Use with `Gen/Midnight.lean`, `Motto.lean`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision Source Wilson
variable {E :Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge}{A D: Sky G}{J:Labels.Jet G}{H:Hol G}{x:E4}{i:Axis}{k d n:ℕ} {Z:Arc ℝ G}{Q Q': Vehicle ℝ G}
local notation "P"=> E4
local notation "U"=> G.mat
local notation "Λ"=> G.lieExp
local notation "Γ"=> G.colorMat
local notation "Cℓ"=>G.Color

lemma messenger (f:Cℓ): fderiv ℝ G.plog (1:G.Mat) ( Γ f )=f:=by
    let X:=G.plog; have he:X ∘ U ∘ Λ =ᶠ[𝓝 0]id:= G.plog_left
    have hv: HasFDerivAt id (( fderiv ℝ X (1:G.Mat) ).comp G.colorMat.toContinuousLinearMap) (0:Cℓ):= by refine HasFDerivAt.congr_of_eventuallyEq ?_ he.symm; refine ( HasFDerivAt.comp (0:Cℓ) ?_ G.expDiff_zero ); exact (show (( U ∘ Λ ) 0)=(1:G.Mat) from by simp only [comp_apply,G.mat_lieExp_zero,G.mat_one]).symm ▸ ( G.plog_diff.differentiableAt (by simp)|>.hasFDerivAt ) -- check at U ∘ Λ
    exact DFunLike.congr_fun ( hv.unique ( hasFDerivAt_id _ ) ) f
-- inner path expressions at fixed x:E4 aligned period
private abbrev ζ (p:P)(s:ℝ):= (s,p,s)
private abbrev wires (Z:Arc ℝ G)(i:Axis)(x:P)(s:ℝ×ℝ): G.Mat:= enter G (drives Z i) ( ζ x s.1,s.2 )
private abbrev lanes (Q:Vehicle ℝ G)(i:Axis)(x:P)(s t:ℝ):= U ( Q i ( ζ x s ) t )
private lemma Farest (hp:Flo Z)(h:Leads Q Z)(i:Axis)(x:P): Engage 0 ( wires Z i x ) ( lanes Q i x ):= by
    let f(t:ℝ×ℝ):= drives Z i ( ζ x t.1,t.2 ); refine ( show Engage 0 (enter G f) _ from Meets.equip ?_ ?_ (meets_into ( h i ) ( ζ x )) ); exact (hp.this i).comp (f:=fun t:ℝ×ℝ=>(ζ x t.1,t.2)) (by unfold ζ; fun_prop); exact fun t=> zero_smul ..
abbrev ribbon (Q:Vehicle ℝ G)(i:Axis)(y:P)(s:ℝ):= alongB Q i (y,s)
lemma Leads.starts (h:Leads Q Z)(hp:Flo Z)(i:Axis)(y:P): ribbon Q i y 0=0:= by unfold ribbon alongB; change G.plog (U (Q i ( (0:ℝ),y,0 ) 1))=_; rw [h.house hp,G.mat_one,G.plog_one]
private lemma slope_C (h:Leads Q Z)(hp:Flo Z)(i:Axis)(y:P): deriv (ribbon Q i y) 0= Z 0 i y:=by
    let X:= wires Z i y; let L(s):=lanes Q i y s 1; obtain ht:= Farest hp h i y; have he: ContDiffAt ℝ ∞ L 0:= ht.smooth; have hu:L 0=1:=ht.base; let γ : G.Color→L[ℝ] G.Mat:= G.colorMat.toContinuousLinearMap
    have hx: deriv L 0= Γ ( Z 0 i y ):= by
       refine (Engage.initial_slope ht).trans ?_
       -- diamonds. f application equivalence by proof terms more than simp.
       refine ( intervalIntegral.integral_congr (show Set.EqOn (fun v:ℝ=> deriv (fun s:ℝ=> X (s,v)) 0) (fun v:ℝ=> Γ (Z 0 i y)) _ from ?_) ).trans ?_
       · intro t _; let f(s:ℝ):= Z s i (y+(s*t) • basis i); have hx:= ( hp i ).comp (f:=fun s:ℝ=>(s,y+(s*t) • basis i)) (by fun_prop); have h':ContDiff ℝ ∞ f:=hx; have hg: HasDerivAt (fun t:ℝ=> t • f t) (Z 0 i y) 0:= by simpa [f] using! ( hasDerivAt_id' (0:ℝ) ).smul (( h'.differentiable ( by simp ) 0 ).hasDerivAt)
         exact ( γ.hasFDerivAt.comp_hasDerivAt 0 hg ).deriv
       rw [ intervalIntegral.integral_const ]; simp
    have hc: HasDerivAt L (Γ ( Z 0 i y )) 0:= ( he.differentiableAt (by simp)|>.hasDerivAt ).congr_deriv hx
    have hd: HasFDerivAt G.plog (fderiv ℝ G.plog 1) ( L 0 ) := hu.symm ▸ ( G.plog_diff.differentiableAt (by simp)|>.hasFDerivAt ); exact ( hd.comp_hasDerivAt 0 hc ).deriv.trans ( messenger .. )
-- powers with variable signal.V.E.
lemma onRail (i:ℕ){f:ℝ→ E}(hp:ContDiffAt ℝ ∞ f 0): Near i (fun t:ℝ=> t^i • f t) (fun t:ℝ=> t^i • f 0):= by
    induction i with
    | zero=> rw [near_first]
    | succ k ih=> unfold Near; rw [ show (fun t:ℝ=> t^(k+1) • f t)=(fun t:ℝ=> t • t^k • f t) from funext fun _=> by rw [pow_succ', mul_smul], show (fun t:ℝ=> t^(k+1) • f 0)=(fun t:ℝ=> t • t^k • f 0) from funext fun _=> by rw [pow_succ', mul_smul] ]; exact ih.weight ( ( contDiffAt_id.pow k ).smul hp ) ( ( contDiffAt_id.pow k ).smul contDiffAt_const )
-- from Good ℓ spacing shift by connection field $a^{n+1}$
-- modify retains Flo.S.
def fixZ (Z:Arc ℝ G)(D:Sky G)(n:ℕ)(s:ℝ): Sky G:= Z s+s^(n+1) • D
lemma lifted (h:Flo Z)(v:Fluid D)(n:ℕ): Flo (fixZ Z D n):= fun i=> ( h i ).add ( show ContDiff ℝ ∞ (fun t:ℝ×P=>t.1^(n+1) • D i t.2) from ( contDiff_fst.pow _ ).smul ( ( v i ).comp contDiff_snd ) )
lemma baseZ (Z:Arc ℝ G)(D:Sky G)(n:ℕ): fixZ Z D n 0=Z 0:=by unfold fixZ; simp
private lemma wires_c (hp:Flo Z)(v:P) (t:ℝ): ContDiff ℝ ∞ ( fun s:ℝ=> wires Z i v (s,t)):=( G.colorMat.toContinuousLinearMap.contDiff.comp ( hp.this i ) ).comp ( f:=fun s:ℝ=>(ζ v s,t)) (by unfold ζ; fun_prop)
-- core formula generic
private lemma wireStep (D:Sky G)(y:P)(v s:ℝ): wires (fixZ Z D n) i y (s,v)= wires Z i y (s,v) + s^(n+2) • Γ ( D i (y+(s*v) • basis i) ):=by
    let A:= Z s i ( y + (s*v) • basis i ); let B:=D i ( y + (s*v) • basis i ); change Γ (s • ( A+ s^(n+1) • B ))= Γ (s • A)+ s^(n+2) • Γ B; rw [ smul_add, map_add, map_smul Γ s (_ • _), map_smul Γ,pow_succ' _ ( n+1 ), mul_smul ]; simp only [map_smul]
private lemma repair_aux (h:Leads Q Z)(h':Leads Q' (fixZ Z D n))(hp:Flo Z)(dH:Fluid D)(i:Axis)(y:P) : Near (n+1) (fun s=>lanes Q' i y s 1) (fun s=>lanes Q i y s 1) ∧ iteratedDeriv (n+2) (fun s=>lanes Q' i y s 1) 0- iteratedDeriv (n+2) (fun s=>lanes Q i y s 1) 0=(( (n+2).factorial :ℝ )) • Γ ( D i y ):=by
    let X:= wires Z i y; let Y:=wires (fixZ Z D n) i y; obtain ht:= Farest hp h i y; obtain hu:= Farest (lifted hp dH n) h' i y; let K(v s:ℝ):= Γ ( D i (y+(s*v) • basis i)); have hK(v:ℝ): ContDiff ℝ ∞ (K v):=( G.colorMat.toContinuousLinearMap.contDiff.comp ( dH i ) ).comp (f:=fun s:ℝ=> y+(s*v) • basis i ) ( by fun_prop );
    have hh (v:ℝ)(k:ℕ)(hk:k≤n+2) : iteratedDeriv k (fun s:ℝ=>Y (s,v)) 0-iteratedDeriv k (fun s:ℝ=> X (s,v)) 0= if k=n+2 then ((( n+2 ).factorial:ℝ)) • Γ ( D i y ) else 0:= by
       rw [ show (fun s:ℝ=>Y (s,v))= (fun s:ℝ=> X (s,v)) + (fun s:ℝ=> s^(n+2) • K v s) from funext fun t=> wireStep D y v t, iteratedDeriv_add ( ( wires_c (i:=i) hp y v ).contDiffAt.of_le ( WithTop.coe_le_coe.mpr le_top ) ) ( show ContDiffAt ℝ k (fun s:ℝ=>s^(n+2) • K v s) _ from ( ( contDiffAt_id.pow _ ).smul ( ( hK v ).contDiffAt ) ).of_le ( WithTop.coe_le_coe.mpr le_top ) ), add_sub_cancel_left, onRail (n+2) (hK v).contDiffAt k hk, lift_symbol ]
       by_cases hh:k=n+2; · subst k; simp [K]
       simp [hh]
    have hb(v:ℝ): Near (n+1) (fun s=>Y (s,v)) (fun s=>X (s,v)):=fun k hk=> sub_eq_zero.mp ( by rw [ hh v k (by omega), if_neg (by omega)] ); refine ⟨ hu.near ht hb,?_⟩; rw [ hu.one_more ht hb, intervalIntegral.integral_congr (show Set.EqOn _ (fun _=>(((n+2).factorial:ℝ) • Γ (D i y))) _ from fun s _=> ( hh s (n+2) le_rfl ).trans ( if_pos rfl )) ]; rw [ intervalIntegral.integral_const ]; simp
-- log-coordinate shift. Expose
lemma step_R (h:Leads Q Z)(h':Leads Q' (fixZ Z D n))(hp:Flo Z)(hd:Fluid D)(i:Axis)(y:P): Near (n+1) (ribbon Q' i y) (ribbon Q i y) ∧ iteratedDeriv (n+2) (ribbon Q' i y) 0 - iteratedDeriv (n+2) (ribbon Q i y) 0=(( (n+2).factorial:ℝ )) • D i y:=by
    obtain ⟨H,Ht⟩:= repair_aux h h' hp hd i y; let f(t):=lanes Q' i y t 1; let g(t):=lanes Q i y t 1; have he:= Farest hp h i y; have hv:= Farest ( lifted hp hd n ) h' i y; have hx: ContDiffAt ℝ ∞ G.plog ( f 0 ):= by rw [show f 0=1 from hv.base]; exact G.plog_diff.of_le le_top
    refine ⟨H.vcomp hv.smooth he.smooth hx,?_⟩; change iteratedDeriv (n+2) ( G.plog ∘ f ) 0-iteratedDeriv ( n+2 ) ( G.plog ∘ g ) 0=_ ; rw [ ahead H hv.smooth he.smooth hx,Ht,show lanes Q' i y 0 1=1 from hv.base,_root_.map_smul ]; exact congrArg (fun x:Cℓ=> (((n+2).factorial:ℝ)) • x) (messenger (D i y))
theorem headS (h:Leads Q Z)(hp:Flo Z)(i:Axis)(y:P): ribbon Q i y 0=0 ∧ deriv (ribbon Q i y) 0=Z 0 i y:=⟨h.starts hp i y,slope_C h hp i y⟩
end YM.FVA2.Gen
