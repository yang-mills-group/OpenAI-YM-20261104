import YM.WilsonCoeffUV.Reclosure.Paths.SignedPackets
/-!
# Graft interface for an E unmasked classical/loop packet

Control from the actual PathData.Bounds. No original clipping or mask tests
at beta; supplied `PCalc/Chart` beta-germ. Match assumption is on the WHOLE
bases. Doesn't supply physical selection or clipping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries
open scoped ContDiff Topology BigOperators InnerProductSpace
variable {G:Gauge}{c:Side}{k r t e:ℕ}{s A B a:ℝ}{C:Clip}{R:PathData G}

-- direct Wilson exact wraps
private def stations (G:Gauge)(p:PlaqAxes)(i:Glimpses G): YForest G:= (squashA G p i).get (by unfold squashA; simp)
lemma moon_wrap (G:Gauge)(k r:ℕ)(n:Side): sprig (eWilson (G:=G) (c:=n)) 2 k (r+1)=lagoon (moon G k (r+1)) n:=by
    by_cases H:2+k=r+1; swap
    · unfold moon sprig; rw [shine_dark H,Finset.sum_apply,Finset.sum_eq_zero,lagoon_none]
      intro i _; ext x; simp [sunflower,worn,Bank.tie,iris,Blue.fade,shine_dark H]
    rw [sprig,H,shine_lit]
    let f (p:PlaqAxes)(x: Site n) (v:Lawn (Co n (Hooks G))) := dut G (casement (squashA G p) x*ᵥ v)
    have hb i x:Green (f i x):=by apply ContDiffAt.comp (g:=dut G) _ _ (board _); simp; apply dut_green
    have hv: eWilson=∑ p:PlaqAxes,∑ x:Site n,f p x:=by
        funext v; unfold eWilson Wilson.energy; simp only [Fintype.sum_prod_type, Finset.sum_apply]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl fun j _=> dut_cost ..)
    have hS i: Green (∑ x:Site n,f i x):= by unfold Green; rw [show (∑ x:Site n,f i x)=fun v=>∑ x:Site n,f i x v from funext fun v=> Finset.sum_apply ..]; apply ContDiffAt.sum; exact fun _ _=>hb _ _
    unfold moon; rw [hv, rye_scoped (fun i _=>hS i),Finset.sum_apply,lagoon_join _ (fun i _=>it_cost (squashA G i) _ _ 1 zero_le_one) one_pos]; apply Finset.sum_congr rfl; intro i _
    rw [rye_scoped (fun _ _=>hb i _),show squashA G i= (some ∘ stations G i) from rfl,sunflower_wrap, iris_apply]; refine Finset.sum_congr rfl fun j _=>?_
    change rye (f i j) (r+1)=Blue.fade (casement (squashA G i) j) (sprig _ 2 k) (r+1)
    have he:=congr_fun (beam (casement (squashA G i) j) (dut G) (dut_green G) (r+1)) (r+1); unfold sprig at he ⊢; rw [Nat.add_zero,shine_lit] at he; rw [H]; exact he

-- combine gram rows, carries every support path pair
abbrev towers (G:Gauge) (_P:PathData G) : ℕ≃ Stationary.PairsIndex := by
    haveI: Nonempty PlaqAxes:= ⟨⟨(0,1),by decide⟩⟩
    exact enumerate _

def tides (P:PathData G): Stack G 0:= gramPath P ∘ towers G P
lemma tides_pay (K:R.Bounds C s A B): SumBudget (fun i=>(tides R i).budget s) (gramCost G A):=budget_copy (towers G R) (gram_budget R (σ:=s) (A:=A) K.rows)
lemma tones (P:PathData G)(j): (tides P j).Invariant:=by
    have h (i:PairsIndex)(x:Fin 2→G.Color) : (gramPath P i).poly x=gramWeight P i* inner ℝ (x 0) (x 1):= by
       unfold Atom.poly; rw [← Equiv.sum_comp (finTwoArrowEquiv G.ColorIndex).symm, Work.F03.inner_color]; simp [gramPath,Fintype.sum_prod_type,Fin.prod_univ_two,finTwoArrowEquiv,ite_mul,Finset.mul_sum]
    intro v x; simp_rw [tides,Function.comp_apply,h]; rw [show inner ℝ (G.adjoint v (x 0)) (G.adjoint v (x 1))=inner ℝ (x 0) (x 1) from (show G.Color→ₗᵢ[ℝ]G.Color from { G.adjoint v with norm_map':= G.norm_adjoint v }).inner_map_map _ _]
lemma tides_cut (K:R.Bounds C s A B)(x:Site c)(U:Config G c):
    (∑' i,(tides R i).unmasked U x)=∑ y,‖R.ell U (x,y)‖^2/2 := (show _ = ∑' b, Stationary.aTerm (gramPath R b) (expandAt x U) from (towers G R).tsum_eq _).trans (gram_sums R K U x)
lemma quarter (K:R.Bounds C s A B)(n:Side):
    quadratic C R=C.direct • Wilson.energy (G:=G) (n:=n)+Precision.uncut (tides R):=by
    funext U; unfold quadratic Wilson.energy Precision.uncut; simp only [Finset.sum_add_distrib,Fintype.sum_prod_type,←Finset.mul_sum,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; simp_rw [tides_cut K]

-- register references

def pool (P:PathData G) : SeriesA G:=
    [⟨0,0,le_rfl,tides P⟩,⟨1,1,le_rfl,P.cubic⟩,⟨2,2,le_rfl,P.quartic⟩,⟨2,0,by omega,P.loop⟩]
lemma tide_chart (K:R.Bounds C s A B):Draw (pool R) s (A+B+gramCost G A):=by
    have hp:=cap_nn K.three; have hb:=cap_nn K.two; have hV:= cap_nn (tides_pay K)
    refine ⟨by linarith,?_⟩; intro i hi
    simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with v|v|v|v<;>subst i
    · exact Commission.change ⟨tones R, tides_pay K, by intro h; change 0< (0:ℕ) at h; omega⟩ le_rfl (by linarith)
    · exact Commission.change ⟨fun i=>(K.invariant i).2.1,K.three,fun _=> trivial⟩ le_rfl (by linarith)
    · exact Commission.change ⟨fun i=>(K.invariant i).2.2,K.four,fun _=> trivial⟩ le_rfl (by linarith)
    apply Commission.change _ le_rfl (show B≤ A+B+gramCost G A by linarith)
    constructor
    · intro n; exact (K.invariant n).1
    · exact K.two
    intro _; change Sprite _; intro i x; constructor
    · have he:=(K.loopTerms i x).1.hasSum; rw [(K.loop_normal i x).1] at he; exact he
    intro k; have he:=((K.loopTerms i x).2 k).hasSum; rw [(K.loop_normal i x).2 k] at he; exact he

-- torment-free germs stamped

def front (R: PathData G)(C:Clip) (n:Side): PChart G n:= sprig (intended C R) 2 + sprig (turnSeries R.loop) 0
def breast (R: PathData G)(C:Clip) : Canvas G:= C.direct • moon G+fun e r=> huesT (murals (pool R) e r)
lemma flip_e (x:Link G c) (v:Signed): Wilson.energy (pull v 0 (input G c x))=eWilson x:=by rw [energy_pull,mantle_input]; rfl
lemma firstTerm (K:R.Bounds C s A B)(n:Side): inputSeries C R (m:=n)= C.direct • eWilson + turnSeries (tides R):=by
    funext x; unfold inputSeries secondTerm turnSeries Patch.average; simp_rw [quarter K n,Pi.add_apply,Pi.smul_apply, Finset.sum_add_distrib,flip_e]; simp
    have hZ: (Fintype.card Signed:ℝ)≠0:=by positivity
    field_simp
lemma shine_plus {U:Type*}(x y:Ten ℝ U r): shine (x+y)=shine x+shine y:=by
    funext i; by_cases h:r=i; subst i; rw [Pi.add_apply,shine_lit,shine_lit,shine_lit]; rw [Pi.add_apply,shine_dark h,shine_dark h,shine_dark h,zero_add]
lemma sprig_plus (f g:Link G c→ℝ)(p: Green f)(u:Green g)(t):sprig (f+g) t= sprig f t+sprig g t:=by funext i; rw [Pi.add_apply,sprig,rye_plus f g p u,shine_plus]; rfl
lemma nilSeed (i:PrismA G)(h:Commission i.cells s A i.grade)(p:0<s)(j:ℕ)(ht:i.grade+j=i.rise+2):
    sprig (turnSeries i.cells (m:=c)) j = surf i c:= by
    set r:= i.rise+2; set m:=i.grade; let f:=turnSeries i.cells (m:=c)
    ext1 v; rw [surf]; split
    · change shine (rye f _)=shine (rye f _); rw [show j+v=i.rise+2+(v-i.grade) by omega]
    next hv=>
        unfold sprig; rw [show rye f (j+v)=0 from ?_]; change shine (0:Ten ℝ (Woods G c) (j+v))=_
        · funext l; by_cases w:j+v=l; subst l; rw [shine_lit]; rfl
          exact shine_dark w
        have he:Green f:= (turns_analytic i.cells p h.toll).contDiffAt
        have hx:= (rays_jet he.analyticAt (i.rise+2)).1 (turns_low i.cells p h.toll) (j+v) (by omega)
        ext1 x; unfold rye; rw [hx]; simp

lemma front_full (K:R.Bounds C s A B)(n:Side): front R C n = C.direct • sprig (eWilson (G:=G) (c:=n)) 2 + sands (pool R) n := by
    unfold front
    let H₁:=score_analytic n R.cubic K.width K.three
    rw [intent C R,firstTerm K n];
    let w:Link G n→ℝ:=eWilson; let G':=C.direct • w
    let a:= turnSeries (tides R) (m:=n); let b:=turnSeries R.cubic (m:=n); let y:=turnSeries R.quartic (m:=n)
    have ha:Green a:= (turns_analytic (tides R) K.width (tides_pay K)).contDiffAt
    have hb:Green b:= (turns_analytic R.cubic K.width K.three).contDiffAt
    have hy:Green y:= (turns_analytic R.quartic K.width K.four).contDiffAt
    have Hw:Green G':= (W_green (c:=n) (G:=G)).const_smul C.direct
    have he:= tide_chart K
    let Q: PrismA G:=⟨0,0,le_rfl,tides R⟩; let X:PrismA G:=⟨1,1,le_rfl,R.cubic⟩
    let Y: PrismA G:=⟨2,2,le_rfl,R.quartic⟩; let B':PrismA G:=⟨2,0,by omega,R.loop⟩
    have hx: pool R=[Q,X,Y,B']:=rfl
    change sprig (((G'+a)+b)+y) _ + _=_
    rw [sprig_plus ((G'+a)+b) y ((Hw.add ha).add hb) hy,sprig_plus (G'+a) b (Hw.add ha) hb, sprig_plus G' a Hw ha, nilSeed Q (he.2 Q (by rw [hx]; simp)) K.width 2 (by rfl),nilSeed X (he.2 X (by rw [hx]; simp)) K.width 2 (by rfl), nilSeed Y (he.2 Y (by rw [hx]; simp)) K.width 2 (by rfl), nilSeed B' (he.2 B' (by rw [hx];simp)) K.width 0 (by rfl)]
    have hv : sprig G' 2=C.direct • sprig w 2:= by
       funext i j; rw [sprig, rye_mu C.direct w W_green]; by_cases h:2+i=j; subst j; simp only [Pi.smul_apply,sprig,shine_lit]
       rw [shine_dark h]; simp only [sprig,Pi.smul_apply,shine_dark h,smul_zero]
    rw [hv]; change _=C.direct • sprig w 2+(surf Q n+(surf X n+(surf Y n+(surf B' n+0))))
    abel
end YM.WilsonCoeffUV.Bank.Mosaic
