import YM.PertExtension.PolynomialWick
import YM.PertExtension.PlateEvaluation
import YM.PertExtension.BlendLeading

/-! From finite diagram (`diagonalWith`, the same tree Jacobian and denominator)
to normalized polynomial Wick overlap on exact shifted orbit sites. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.LatticePT.Node
open Function Filter Set Wilson Lattice RG MeasureTheory Orb GaussianScore Gauge MvPolynomial Finset Next.Rank Next.Rank.Normal
open Chart Series Series.Tested Source Bid Labels Heat Heat.Top Slope Mixed Leading
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{I:Type*}[Fintype I](s: Finset I)(v:I→Word G)(o:I→Site n)(t:Task v)(ε:ℝ)

abbrev bareFactor (u:Word G)(j:u.F.Index): poly (Atom G) := (topMatrix u.S u.H u.sound u.chosen).basis j

def pricedBare : poly (I×Atom G):=pot univ fun i=> (↑((v i).cost (t i) ε):ℂ) • (bareFactor (v i) (t i))

def probe (j:I×Atom G) := leg (o j.1) j.2

def jointFinite := SlopeWick.formed (probe (G:=G) o)

lemma joint_matches (X:I→Cover): jointFinite (G:=G) (fun i=>wrap n (X i))= fun e=>
    ⟨(fun a b=>(↑((echo n (X a.1) (X b.1) (atAddress a.2) (atAddress b.2)):ℝ):ℂ)),(by intro a b;rw [echo_comm e])⟩:=by
   funext e
   apply Symmetric.ext;funext a b;rw [(jointFinite _ _).symm a b];dsimp only [jointFinite,SlopeWick.formed]; exact congr_arg Complex.ofReal (Slope.cov (G:=G) e (X a.1) (X b.1) a.2 b.2)



private lemma leaf_limit (x:Orb.Dir G n) (i:I) :
 Tendsto (fun r:ℝ=> r⁻¹^((v i).F.grades (t i)).2 * ((v i).cost (t i) ε * SlotEvaluation.fieldAt (v i).S (t i) (o i) (representative (r•x)))) (𝓝[>] 0) (𝓝 ((aeval (fun j:Atom G=> (leg (o i) j x:ℂ)) ((↑((v i).cost (t i) ε):ℂ) • bareFactor (v i) (t i))).re)) := by
    have he:=priced_basis (o i) x (v i).F (rendered _ (v i).chosen).toData (v i).S (rend_acts (v i).sound (v i).chosen) (t i)
    convert! he.const_mul ((v i).cost (t i) ε) using 2
    · ring
    rw [map_smul];simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero];rfl

include s
private lemma overlap_limit (x:Orb.Dir G n) : Tendsto
   (fun r:ℝ=> r⁻¹^number v t * ((Mixed.product v Finset.univ t o ε) (representative (r•x)))) (𝓝[>] 0) (𝓝 ((aeval (fun j: I×Atom G=>(probe o j x:ℂ)) (pricedBare v t ε)).re)) := by
    let T i:= leaf_limit v o t ε x i
    let F i(j:(v i).F.Index):=bareFactor (v i) j
    let p:=(pricedBare v t ε); let L i:ℂ:=((v i).cost (t i) ε : ℝ); let H i:=aeval (R:=ℂ) (fun j:Atom G=> (leg (o i) j x:ℂ)) (L i • F i (t i))
    have hy i: star (H i)=H i:=by
       have hh := Vertex.basis_real (v i).S (v i).H (v i).sound (v i).chosen (t i) (fun j => letterPolar (Slope.address (o i) j) x)
       unfold H; rw [map_smul,smul_eq_mul,Complex.star_def,map_mul]; unfold Hue.display at hh
       have hpq : (fun j:Atom G=> (leg (o i) j x:ℂ))=(fun j: Atom G=> ↑( (letterPolar (Slope.address (o i) j.1) x j.2):ℝ)) :=funext fun j=>congr_arg _ (EuclideanSpace.basisFun_inner G.ColorIndex ℝ (letterPolar (Slope.address (o i) j.1) x) j.2)
       rw [hpq, show (starRingEnd ℂ) (L i)=L i from Complex.conj_ofReal _]; exact congr_arg₂ (· * ·) rfl hh
    have hz: (aeval (R:=ℂ) (fun i=>(probe (G:=G) o i x:ℂ)) p:ℂ).re=(∏ i,H i).re:=by unfold p pricedBare pot; rw [map_prod];refine congr_arg Complex.re (Finset.prod_congr rfl (fun i _=>?_)); unfold post; rw [aeval_rename];rfl
    have hp: (∏ i,H i).re=∏ i,(H i).re := by
       have hp: (↑(∏ i,(H i).re):ℂ)=∏ i,H i:=by rw [Complex.ofReal_prod];exact Finset.prod_congr rfl fun i _=>Complex.conj_eq_iff_re.mp (hy i)
       rw [←hp, Complex.ofReal_re]
    have hL:=tendsto_finset_prod univ (fun i _=>T i)
    rw [(hz : (aeval _ (_:poly _) : ℂ).re=_),hp]
    apply hL.congr fun r=>?_
    unfold number Mixed.product; rw [← prod_pow_eq_pow_sum,prod_mul_distrib]

omit s
lemma jetRadial (x:Orb.Dir G n):
    Radial.jet ((restrictedO (Mixed.product v univ t o ε)) ∘ Chart.expLinks G (Cotree n)) (number v t) x=(aeval (R:=ℂ) (fun i=>(probe (G:=G) o i x:ℂ)) (pricedBare v t ε)).re:=by
    let O:=Mixed.product v univ t o ε
    obtain ⟨hv,hd⟩:=Mixed.product_good v t (n:=n) o ε
    have hC:=hv.curved.germ
    have ha:= directions hC x
    have ht: Aspiration (fun r:ℝ=>r⁻¹^number v t * O (representative (r•x))) (fun i=>Radial.jet ((restrictedO O) ∘ Chart.expLinks G (Cotree n)) (number v t+i) x):= ha.shift fun i hi=>congr_fun (jets_vanish hC hd hi) x
    exact tendsto_nhds_unique (ht.tendsto_first) (overlap_limit (univ) v o t ε x)

lemma diagonal_leading (h:Even n.val) : diagonalWith (tray G) (restrictedO (Mixed.product v univ t o ε)) (number v t+0) = (blend (jointFinite o h) 0 (pricedBare v t ε)).re:= by
    let O:=Mixed.product v univ t o ε
    let E:= (gaussian h fun x=>(aeval (R:=ℂ) (fun i => (probe (G:=G) o i x:ℂ)) (pricedBare v t ε)).re)
    have h1:= (show LocalTest (restrictedO O) from (Mixed.product_good v t (n:=n) o ε).1.curved)
    rw [add_zero,leading_row (traySpec G) h1 (Mixed.product_good v t ..).2 h]
    refine Eq.trans ?_ (b:=E) ?ans
    case ans => exact SlopeWick.expansion (probe o) h (pricedBare v t ε)
    unfold O E gaussian Law.average
    simp_rw [jetRadial, saddleLaw h];rfl
end YM.PertExtension.LatticePT.Node
