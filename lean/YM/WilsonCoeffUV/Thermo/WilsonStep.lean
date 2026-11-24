import YM.WilsonCoeffUV.Thermo.Templates
/-! Wilson stencil and per-link density stencil. No extra sym. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n:Side}
variable {α U: Type*}

section ray
variable [DecidableEq α][Fintype α]
lemma sight_step (p:Leads Cover α U)(x:Site n)(j:U)(k)(h:p j=some k)(y:Lawn (Co n α)):
    (casement p x *ᵥ y) j=y (jog x (foldUnder n k)) := by
  change dotProduct (casement p x j) y=_; unfold casement; rw [plank_origin _ _ j (show _=some (foldUnder n k) from by simp [Function.comp_apply,h]),single_dotProduct,one_mul]
lemma sight_none (p:Leads Cover α U)(x:Site n)(j:U)(h:p j=none)(y:Lawn (Co n α)): (casement p x*ᵥ y) j=0:=by
  change dotProduct (casement p x j) y=_; unfold casement; rw [plank_blank _ _ j (by simp [Function.comp_apply,h]), zero_dotProduct]
end ray
abbrev Hooks (G:Gauge):= PAC G 1
abbrev YForest (G:Gauge):= Cloth (Hooks G)

-- log Haar

def blumeA (Ñ : ChartRatio G)(x:Lawn G.ColorIndex) := Real.log (dij Ñ x)
def bekon (G:Gauge)(j:Axis): Leads Cover (Hooks G) G.ColorIndex:= fun i=>some (0,coord j,i)
lemma beckons (p:Site n)(v:Axis)(x:TreeVars G n): casement (bekon G v) p *ᵥ x= dyes x (p,v):=by ext i; rw [sight_step _ p i (0,coord v,i) rfl]; change x (p+wrap n 0,coord v,i)=x _; rw [map_zero,add_zero]; rfl
lemma blume_green {Ñ:ChartRatio G}(h:LocalRatio Ñ) : Green (blumeA Ñ):= (dij_green h).log (by rw [dij,map_zero,h.anchored]; norm_num)
def bearingJ (Ñ: ChartRatio G)(k:ℕ): Gen ℝ (YForest G):= ∑ v:Axis, sunflower (bekon G v) (sprig (blumeA Ñ) 0 k)
lemma bloom_pages {Ñ:ChartRatio G}(h:LocalRatio Ñ)(k r): Yields (fun n=> sprig (unhaar (n:=n) Ñ) 0 k r) (bearingJ Ñ k r):= by
  apply daisies (I:=G.ColorIndex) (h:=fun v=>blume_green h) (A:=bekon G) (H:=fun _=>unhaar_green h)
  intro n; apply Eventually.of_forall; intro v; unfold unhaar; rw [Fintype.sum_prod_type,Finset.sum_comm]; exact Finset.sum_congr rfl (fun j _=>Finset.sum_congr rfl fun i _=> by rw [beckons]; rfl)
lemma bloom_bill (Ñ:ChartRatio G) (k r : ℕ)(s:ℝ)(h:0≤s): ∃ A:ℝ, Amber terrain s A (bearingJ Ñ k r):=by
  choose A he using fun v : Axis => it_cost (bekon G v) (sprig (blumeA Ñ) 0 k) r s h
  rw [bearingJ,Finset.sum_apply]; exact ⟨_,Amber.sum _ (fun i _=> he i)⟩

-- actual top face stencil. Use four oriented bases, no 4 factors implicit.
abbrev Glimpses (G:Gauge):= Fin 4×G.ColorIndex

def squashA (G:Gauge)(p:PlaqAxes): Leads Cover (Hooks G) (Glimpses G):=fun i=>
    let u:=p.val.1; let v:=p.val.2; let w:Fin 4→ Cover×TypeFace 1:=![ (0,coord u), (step u,coord v),(step v,coord u),(0,coord v)]
    some ((w i.1).1,(w i.1).2,i.2)

def dots (x:Lawn (Glimpses G))(i:Fin 4):=G.lieExp (coatC G fun j=>x (i,j))
def dut (G:Gauge)(x:Lawn (Glimpses G)):= G.price (dots x 0*(dots x 1*((dots x 2)⁻¹*(dots x 3)⁻¹)))
lemma dut_green (G:Gauge): Green (dut G):= by
  have hx (i:Fin 4) : Green fun x:Lawn (Glimpses G)=>G.mat (dots x i):= G.exp_jet.contDiffAt.comp (f:=fun x:Lawn (Glimpses G)=>coatC G fun j=>x (i,j)) 0 ((coatC G).contDiff.contDiffAt.comp _ (contDiffAt_pi.mpr fun _=>contDiffAt_apply ℝ ℝ _ _))
  unfold Green dut; apply Work.F03.price_smooth (A:=fun x:Lawn (Glimpses G)=> (dots x 0*(dots x 1*((dots x 2)⁻¹*(dots x 3)⁻¹))))
  simp_rw [G.mat_mul, G.mat_inv]; exact (hx 0).mul ((hx 1).mul (((starL ℝ).contDiff.contDiffAt.comp _ (hx 2)).mul ((starL ℝ).contDiff.contDiffAt.comp _ (hx 3))))
lemma dut_cost (p:PlaqAxes)(v:Site n)(x:TreeVars G n): G.price (faceValue (mantle x) (v,p)) = dut G (casement (squashA G p) v*ᵥ x):=by
  rcases p with ⟨⟨a,b⟩,hp⟩
  let p:PlaqAxes:=⟨(a,b),hp⟩
  let X:=casement (squashA G p) v*ᵥ x
  have hh (u:Cover)(j:Axis)(i:Fin 4)(h:∀ k,squashA G p (i,k)=some (u,coord j,k)): mantle x (v+wrap n u,j)=dots X i:= by
    rw [mantle,Work.F03.represent_link,dots]; congr 1; ext k; exact (sight_step (squashA G p) v (i,k) (u,coord j,k) (h k) x).symm
  have h₁ := hh 0 a 0 (fun _=>rfl); have h₂:= hh (step a) b 1 (fun _=>rfl); have h₃:= hh (step b) a 2 (fun _=>rfl); have h₄:= hh 0 b 3 (fun _=>rfl)
  rw [map_zero,add_zero] at h₁ h₄; rw [wrap_step] at h₂ h₃
  unfold faceValue square travel; simp [travel]; rw [show v+step a+step b-step a =v+step b by abel, show v+step a+step b+ -step a-step b=v by abel,h₁,h₂,h₃,h₄]; rfl

def moon (G:Gauge)(k:ℕ): Gen ℝ (YForest G):= ∑ p:PlaqAxes,sunflower (squashA G p) (sprig (dut G) 2 k)
lemma moon_pages (G:Gauge)(k r): Yields (fun n=>sprig (eWilson (G:=G) (c:=n)) 2 k r) (moon G k r):=by
  apply daisies (I:=Glimpses G) (h:=fun _=>dut_green G) (A:=squashA G) (H:=fun _=> W_green)
  intro n; apply Eventually.of_forall; intro x; unfold eWilson Wilson.energy; rw [Fintype.sum_prod_type, Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> dut_cost ..
lemma moon_bill (G:Gauge)(k r : ℕ)(s:ℝ)(h:0≤s): ∃ A:ℝ,Amber terrain s A (moon G k r):=by
  choose A he using fun p=> it_cost (squashA G p) (sprig (dut G) 2 k) r s h
  rw [moon,Finset.sum_apply]; exact ⟨_,Amber.sum _ (fun i _=>he i)⟩
end YM.WilsonCoeffUV.Bank
