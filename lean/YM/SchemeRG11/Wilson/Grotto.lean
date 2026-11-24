import YM.SchemeRG11.Wilson.Starlit
/-! Polynomial renamings & exact near estimate. Action weight logic. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G : Gauge} {N : Side}
variable {I J B U:Type*}

def glen(s:Finset I)(p:I→vellum G): Paper (I×Shaft G) ℝ:= ∏ i∈s,rename (fun u:Shaft G=>(i,u)) (p i)
lemma spell (g:I→Shaft G→U) (s:Finset I)(p:I→vellum G): rename (fun v:I×Shaft G=>g v.1 v.2) (glen s p)=∏ i∈s,rename (g i) (p i):=by
 unfold glen; rw [_root_.map_prod]; apply Finset.prod_congr rfl; intro i _
 rw [rename_rename];rfl
lemma crossing (p:vellum G)(z:Cover)(A:trunk G ℤ) : aeval (cant A) (cross z p)=aeval (cant (fun a=>A (a.1+z,a.2))) p:=by rw [cross,aeval_rename];rfl
lemma honour(x:Cover)(i j:Axis): cross (G:=G) x (Tree.cost 0 i j)=Tree.cost x i j:=by
 apply viewers; intro A; rw [crossing,supper,supper]; unfold First.costVertex; split
 · unfold First.curlAt First.Vleft First.Xleft First.Vright First.Xright First.bracketAt; simp [First.Vleft, First.Xleft, First.Vright, First.Xright,add_comm]
 rfl

variable {T: Itinerary}{o:StepPath T}
def sorted (n:ℕ)(t:I→ℕ→Cover)(r: I×Shaft G): Shaft G:= rise (t r.1 n) r.2
lemma sift (p:Paper (I×Shaft G) ℝ)(t : I→ℕ→Cover)(hw:∀ i,Medium T (t i))(h:Interior T o):
 Tile.Capped (fun k=> (land G).avg (rename (sorted k t) p)) ∧ Flat T (fun k=> (spray G _).avg (adsorb (o k) (rename (sorted k t) p)) - (land G).avg (rename (sorted k t) p)):=by
 let f i := sorted (G:=G) i t; let D i: Dose (I× Shaft G) ℝ:= (land G).pull (Dose.arrow (f i)); let N i:= (spray G _).pull (Dose.arrow ((veil (o i)) ∘ f i))
 have hp i: (land G).avg (rename (sorted i t) p)= (D i).avg p:=by rw [Dose.rebase,Dose.colour]
 have hq i:(spray G _).avg (adsorb (o i) (rename (sorted i t) p)) = (N i).avg p:=by rw [adsorb,rename_rename,Dose.rebase, Dose.colour]
 simp_rw [hp,hq]
 apply trails p
 · intro i j; unfold D; simp_rw [Dose.reach]; apply capLand
 intro i j; dsimp only [D,N]; simp_rw [Dose.reach]; exact mist h (hw i.1) (hw j.1)

def aerial(s:Finset I)(p:I→vellum G)(t:I→ Cover):=∏ i∈s,cross (t i) (p i)
lemma brushed (p:I→vellum G)(s: Finset I)(t:I→ℕ→Cover)(hw:∀ i,Medium T (t i))(h:Interior T o): Flat T (fun k=> (spray G _).avg (adsorb (o k) (aerial s p fun i=>t i k)) - (land G).avg (aerial s p (fun i=> t i k))):=by
 have H(k:ℕ): rename (sorted k t) (glen s p)=aerial s p (fun i=> t i k):= spell (fun i=> rise (t i k)) s p
 simp_rw [←H]; exact (sift _ _ hw h).2
lemma anchored (p:I→vellum G)(s:Finset I)(t:I→ℕ→Cover)(hw:∀ i,Medium T (t i))(h:Interior T o)(i j:Axis)(u:ℕ→Cover)(hu:Medium T u):
 Flat T (fun k=> (spray G _).avg (adsorb (o k) (Tree.cost (u k) i j * aerial s p (fun l=>t l k))) - (land G).avg (Tree.cost (u k) i j * aerial s p (fun l=>t l k))):=by
 let C (v:Option I):=match v with | none=> (Tree.cost 0 i j:vellum G) | some v=>p v
 let W(v:Option I):= match v with | none=>u | some v=>t v
 let S:= Finset.insertNone s
 have ht(a:Option I): Medium T (W a):=by
   cases a; · exact hu
   exact hw _
 have he(k): aerial S C (fun l=> W l k)=Tree.cost (u k) i j * aerial s p (fun l=> t l k):=by
   unfold S aerial; simp only [Finset.prod_insertNone, C,W, honour]
 simp_rw [←he]; exact brushed C S W ht h
lemma lookback (p: Orb.Potential G N)(x:Site N)(i: Axis): Orb.positiveLinks p (-x-step i,i)= (Orb.positiveLinks p (x,i))⁻¹:=by
 unfold Orb.positiveLinks
 have he:= p.property (x,i); change p.val (-x-step i,i)= -p.val (x,i) at he; rw [he, Work.F03.exp_neg_color]

def mirror (i j:Axis)(x : Site N): Site N:= -x-step i-step j
lemma mirror_inv(i j:Axis): Function.Involutive (mirror (N:=N) i j):=fun x=> by unfold mirror;abel
lemma intent(i j:Axis)(x : Site N)(p:Orb.Potential G N): G.price (Orb.plaquette p (mirror i j x) i j)= G.price (Orb.plaquette p x i j):=by
 let y:= mirror i j x; let A:= Orb.positiveLinks p
 have hx:A (y,i)=(A (x+step j,i))⁻¹:=by rw [show y=-(x+step j)-step i from by unfold y mirror; abel]; exact lookback p _ _
 have hy:A (y+step i,j)=(A (x,j))⁻¹:=by rw [show y+step i= -x-step j by unfold y mirror; abel]; exact lookback p _ _
 have hu:A (y+step j,i)=(A (x,i))⁻¹:=by rw [show y+step j= -x-step i by unfold y mirror; abel]; exact lookback p _ _
 have hv:A (y,j)=(A (x+step i,j))⁻¹:=by rw [show y=-(x+step i)-step j by unfold y mirror; abel]; exact lookback p _ _
 change G.price (A (y,i)*A (y+step i,j)*(A (y+step j,i))⁻¹*(A (y,j))⁻¹)= G.price (Orb.plaquette p x i j); rw [hx,hy,hu,hv,inv_inv,inv_inv]
 let D:=A (x,i)*A (x+step i,j); let C:= (A (x+step j,i))⁻¹ * (A (x,j))⁻¹
 rw [show (A (x+step j,i))⁻¹ * _ * A (x,i)* A (x+step i,j)=D⁻¹*(D*C)*(D⁻¹)⁻¹ from by unfold D C; group, G.price_conj]; unfold D C; rw [← mul_assoc (A (x,i)*_)]; rfl
lemma mirror_valid (i j:Axis)(x:Site N)(p:Orb.Potential G N): aeval (cant p.val) (Tree.cost (mirror i j x) i j)=aeval (cant p.val) (Tree.cost x i j):=by
 rw [supper,supper]; by_cases h:i<j
 · apply congrArg (1/2 * ·)
   apply mul_left_cancel₀ (show (3:ℝ)≠0 by norm_num); rw [← First.mask_third _ i j p,← First.mask_third _ i j p]
   apply congrArg (fun f:ℝ→ℝ=> iteratedDeriv 3 f 0); funext t; unfold First.price_at; rw [if_pos h, if_pos h]; apply intent
 simp only [First.costVertex,h,↓reduceIte]
lemma mirror_avg(i j:Axis)(x:Site N)(p:Paper (Pill G N) ℝ): (spray G N).avg (Tree.cost (mirror i j x) i j * p)= (spray G N).avg (Tree.cost x i j * p):=by
 apply Complex.ofReal_injective; simp_rw [←announce,map_mul,mirror_valid]
end YM.SchemeRG11.Acorn
