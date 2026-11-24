import YM.FVA2.Lambda.Peonies
/-!
# SCC. Thermal cost vanishes exactly before radial integration

 Rank-five contraction at q away from 0 is target; ∫ t. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.RoseS
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open Canvas (quad high top_quad line4 triple upperquad trigger)
open Area Shells
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "g"=>triple G
local notation "Ψ"=>field (parity (A:=Axis) (C:=G.ColorIndex))
variable (D E:ℝ→ℝ)(q:QP)(i j k l:G.ColorIndex)(a b:Axis)(w r:List (Lane4 G))(F:Law G)
def I₀ (w:List (Lane4 G)) : Prop:= ∀ l∈w,l.2=0
lemma iq {w:List (Lane4 G)}(h:I₀ w): net w=0:= by
    induction w with | nil=> rfl| cons i w ih=> rw [ net_cons,h i (by simp),ih (fun i hi=> h i (by simp [hi])),zero_add ]
lemma birth_tr (w:List (Lane4 G))(hw:I₀ w): trc (line4 G D) q (quad G E g F) w= scatter Ψ w (fun l r=>Area.first D E g F q l r+Area.first D E g F (-q) l r):= by
    rw [ Flux.at_trc ]; simp_rw [Bead.A_quad,scatter_cons ]; let A:=allocate Ψ w (R:=ℂ)
    let f i j l r:= Bead.attach E g F ((i,q)::(j,-q)::l) r + cross (parity i) (degree Ψ ((j,-q)::l))*Bead.attach E g F ((j,-q)::l) ((i,q)::r) + cross (parity j) (degree Ψ l)*( Bead.attach E g F ((i,q)::l) ((j,-q)::r) + cross (parity i) (degree Ψ l)*Bead.attach E g F l ((i,q)::(j,-q)::r))
    change ∑ i,∑ j,line4 G D i j q • A (f i j)=_
    simp_rw [ ← map_smul, ← map_sum ]; apply scatter_congr; intro l r h; obtain he:net l=0 := iq (fun i h₀=> hw i ( ( split_perm h ).mem_iff.mp ( by simp [h₀] ) ) )
    rw [← Area.second ]; unfold Area.first; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold f piece; rw [Bead.a_guard E _ _ (l:= l) he, Bead.a_guard E _ _ (l:= (i,q)::(j,-q)::l ) (by simp only [net_cons, he, add_zero, add_neg_cancel]) ]; simp only [degree_cons,field]; ring
lemma firstL {l r:List (Lane4 G)}(h:l.length≠1): Area.first D E g F q l r=0:= by unfold Area.first piece; refine Finset.sum_eq_zero (fun i _=> Finset.sum_eq_zero (fun j _=>?_ )); rw [ Bead.boundedL (l:=(i,q)::l) E F (by rw [List.length_cons]; omega) ]; ring
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y) {s t:ℝ}
include hm
abbrev SCC (i j k:G.ColorIndex): List (Lane4 G):= [ (S₀ i,0), (C₀ j,0),(C₀ k,0) ]
lemma θL : trc (line4 G D) q ( quad G E g ( high X 2 (s,t) ) ) ( SCC i j k )=0:= by
    rw [ birth_tr D E q (high X 2 (s,t)) _ ( by intro m hm; simp only [ SCC, List.mem_cons, List.not_mem_nil,or_false ] at hm; rcases hm with h|h|h <;> rw [h] ) ]; let F:=high X 2 (s,t); let P(p:QP):= Area.first D E g F p
    change scatter Ψ _ (fun l r=> P q l r+P (-q) l r)=0
    have he (p:QP)(m h₀:Lane4 G)(l r:List (Lane4 G)): P p (m::h₀::l) r=0:= firstL D E p _ (by simp)
    have ht (p:QP)(r): P p [] r=0:= firstL D E p _ (by simp) -- order
    have hp p: P p [( S₀ i, 0 )] [(C₀ j, 0), (C₀ k, 0)]=0:= respect D E p j k i hm
    have hh p v r: P p [(C₀ v,0)] r=0:= worm_C ..
    simp only [ SCC,scatter_cons,scatter_nil,ht,he,hp,hh,add_zero,mul_zero ]
lemma tall₃ (D:ℝ→ℝ)(hc: net w=0)(ht:w.length=5): quad G D (high X 2 (s,t)) (high X 1 (s,t)) w= quad G D ( high X 1 (s,t)) ( high X 2 (s,t) ) w ∧ quad G D ( high X 1 (s,t) ) (high X 2 (s,t)) w= quad G D g (high X 2 (s,t)) w:= by
    constructor
    · apply Bead.quad_comm D _ _ _ hc <;> exact Bead.prude_solid _ ((Outlook.dock hm wisdom).master.trueC ..)
    rw [Bead.A_quad,Bead.A_quad]; apply scatter_congr; intro l r h; obtain hz:=split_length h; unfold Bead.attach; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold Bead.summit; dsimp only; by_cases hL:l.length=0; · rw [ show high X 2 (s,t) ((j,- -net l)::r)=0 from Canvas.fromD hm 2 s t _ (by rw [List.length_cons]; omega) ]; ring
    rw [ show high X 1 _ ((i,-net l)::l)=_ from Canvas.opens hm _ ((i,-net l)::l) (by rw [List.length_cons]; omega) ]
lemma highS : trc (line4 G D) q (high X 3 (s,t)) ( SCC i j k )=0:= by
    let w c d :=(c,q)::(d,-q):: SCC i j k; let T(t:ℝ):= trc (line4 G D) q (high X 3 (s,t)) ( SCC i j k ); let U(t:ℝ):= trc (line4 G D) q ( trigger X 3 (s,t) ) ( SCC i j k )
    have hc c d : net (w c d)=0:= by simp [w,SCC,net]
    have he t c d : trigger X 3 (s,t) ( w c d )= 2 * quad G ( hot t ) g (high X 2 (s,t)) (w c d):= by obtain hx:= tall₃ (s:=s) (t:=t) (w c d) hm ( hot t ) ( hc c d ) rfl; rw [Canvas.thermal₃, Canvas.cycle0 hm _ _ _ _ (by simp [w,SCC]),hx.1,hx.2]; ring -- coefficient not half?
    have hd(t:ℝ) : HasDerivAt T 0 t:= by
        have hp c d : HasDerivAt (fun t=> high X 3 (s,t) (w c d)) (trigger X 3 (s,t) (w c d)) t:= Canvas.steam hm s (fun _=> hc c d) (by simp [w,SCC]) (by decide) t
        have ht : HasDerivAt T ( U t ) t:= by unfold T U; simp only [at_trc]; exact HasDerivAt.fun_sum (fun i _=>HasDerivAt.fun_sum (fun j _=> (hp i j).const_mul _))
        suffices h : U t=0 from h ▸ ht
        unfold U; rw [at_trc, show (0:ℂ)= (2:ℂ) * trc (line4 G D) q ( quad G ( hot t ) g (high X 2 (s,t)) ) ( SCC i j k ) from by rw [θL D _ _ i j k hm,mul_zero]] -- RHS rewrite
        rw [at_trc]; simp_rw [ Finset.mul_sum ]; apply Finset.sum_congr rfl; intro c _; refine Finset.sum_congr rfl fun d _=>?_ ; convert! mul_left_comm _ (2:ℂ) _ using 1; exact congr_arg₂ (·*·) rfl (he t c d)
    apply Canvas.regression (f:=T) t hd; unfold T; simp_rw [ at_trc ]; have hp (c d:BH G): Tendsto (fun t=> line4 G D c d q * high X 3 (s,t) (w c d)) atBot (𝓝 0):= by obtain he:= (Canvas.down hm ( n:=3) s (fun _=>hc c d) (by simp [w,SCC]) (by decide) (by have hs:= length_pay (w c d); rw [ show ( w c d ).length=5 from rfl ] at hs; omega) ).const_mul (line4 G D c d q); rw [mul_zero] at he; exact he
    simpa only [ Finset.sum_const_zero ] using tendsto_finsetSum (Finset.univ) (fun c _=> tendsto_finsetSum Finset.univ (fun d _=> hp c d ))
lemma point : Mark.token ( trigger X 3 (s,t) ) i j k=0:= by
    change trigger X 3 (s,t) ( SCC i j k )=_
    have hp (F H:Law G): quad G ( hot t ) F H ( SCC i j k )=0:= by obtain he:= Canvas.on_tree G (hot t) F H ( SCC i j k ); rw [show Canvas.onset ( SCC i j k )= SCC i j k from ( by simp [Canvas.onset,SCC] ) ] at he; exact he
    rw [Canvas.thermal₃,hp,hp,add_zero,add_zero]; unfold cycle; simp only [ highS _ _ i j k hm, integral_zero ]
end YM.FVA2.Lambda.RoseS
