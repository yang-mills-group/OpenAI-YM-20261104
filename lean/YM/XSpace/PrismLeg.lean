import YM.XSpace.Ranges
/-! # Physical line outposts and cubic completion at the constant-curvature ports -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chiral
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Structure1 Source Source.Drops Wilson Labels Scale MvPolynomial Pages RG
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}{d:ℕ}{H:Hol G}(h:G.Simple)(S:Survey G H d)(σ:Bool)(p:Name G)
variable (A: Trace.Contact G)
abbrev bellL (σ:Bool)(p:Name G) := Fq σ p.1
def wickLine:= ∑ i:Fin S.size, let k:=S.looks i; coupon h S σ p.1 i • Trace.touch k.offset (six k.plaq) (endr k.plaq) [] p.2
abbrev cable (z:Cover) := displace z (wickLine h S σ p)
lemma valueL : Trace.probe (wickLine h S σ p) A=axial σ p.1 d (primary S (0:Cover) A) p.2 := by
  rw [primary_at,reveal h,WithLp.ofLp_sum, Finset.sum_apply,wickLine,map_sum,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [_root_.map_smul,LinearMap.smul_apply, paid]; let k:= S.looks i
  change _ • (crackle (six k.plaq) (endr k.plaq) A k.offset p.2)= _ * ((linearFace (k.offset,k.plaq) A) p.2); rw [plot (six _) (endr _) k.plaq.property];rfl
lemma initiated : p0 S (0:Cover) (On.lifting (spark σ p))=harp (wickLine h S σ p):=same fun A=>by rw [awake0,axis_power,leg_test,valueL]
lemma translatedL (z:Cover): p0 S z (On.lifting (spark σ p))= harp (cable h S σ p z):= by rw [cable,← rings,← initiated, Trace.stained, Outline.Chart.pull0]; simp [Outline.Chart.lug]
lemma carriesL : wickLine h S σ p∈ cane 1 G:=by unfold wickLine; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (touch_cane _ _ _ [] p.2)
lemma wakesL : Stops (wickLine h S σ p):=by intro v; rw [valueL, ← show Chart2.grad v= stream v from rfl,primary_gradient,map_zero];rfl

-- quadratic completion at this literal angle
def brace (z:Cover): Mu.Stamp G:= p1 S z (On.lifting (spark σ p))
lemma brace_value (z:Cover): pit A (brace S σ p z)=↑((axial σ p.1 d (secondary S z A)) p.2):=by rw [brace,awake1]; exact helper _ _ _ () (EuclideanSpace.proj p.2) (axial σ p.1 d) (fun A=> axis_power σ p A)
where helper {E: Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (f:E→ℂ)(u v:E)(_S:Unit:=()) (P:G.Color→L[ℝ]ℝ) (L:E→ₗ[ℝ] G.Color) (H: ∀ x, f x=(P (L x):ℂ)): fderiv ℝ f u v= (P (L v):ℂ):= by rw [show f=(Complex.ofRealCLM ∘L P ∘L L.toContinuousLinearMap) from funext fun x=> H x]; rw [ContinuousLinearMap.fderiv]; rfl
lemma brace_move (z: Cover): brace S σ p z=Trace.volume z (brace S σ p 0):=by unfold brace; rw [stained,Outline.Chart.pull1]; simp [Outline.Chart.lug]

-- constant values precisely commutator because holonomy core; independent of offset. ALL σ

def brackets (p:P) (A:Axis→G.Color): G.Color:=∑ u:PlaqAxes, q σ p (six u) (endr u) • G.ad (A (six u)) (A (endr u))
lemma traced (p:P)(T:PlaqAxes→G.Color)(H:2≤d): (∑ i:Fin S.size,coupon h S σ p i • T (S.looks i).plaq)=∑ u:PlaqAxes,q σ p (six u) (endr u) • T u:=by simp_rw [← remembrance h S σ p H,Finset.sum_smul,ite_smul,zero_smul]; rw [Finset.sum_comm]; simp
lemma bans (t:ℝ)(a:GaugePanel G S.size): curvature2 S (t • a)=t^2 • curvature2 S a:= by unfold curvature2; rw [helper]; rw [smul_comm]
where helper {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F] (b:E→F)(x:E): iteratedFDeriv ℝ 2 b 0 (fun _=>t • x)=t^2 • iteratedFDeriv ℝ 2 b 0 (fun _=>x):=by simp_rw [iteratedFDeriv_two_apply,map_smul,smul_apply,smul_smul,pow_two]
lemma shut : curvature2 S 0=0:=by have ht:= bans S 0 0; simpa using ht
include h in
lemma brace_receipt (A:Axis→G.Color)(z:Cover)(he:2≤d): pit (A ∘ Prod.snd) (brace S σ p z)=↑((brackets σ p.1 A) p.2):=by
  have he'(x: Cover)(a:PlaqAxes): linearFace (x,a) (A ∘ Prod.snd)=0:=by simp only [angular,Function.comp_apply]; abel
  let P:= A ∘ (Prod.snd (α:=Cover)); have hh: spectra S z P=0:=funext fun i=> he' (stop z (S.looks i).walk) (S.looks i).plaq
  have ht(k:RG.Slot): take2 k z P= G.ad (A (six k.plaq)) (A (endr k.plaq)):=by
    let x:= stop z k.walk; simp only [take2,roundTrip,Drift.conjugate,slotPoint]; rw [native,face_a, face_c,show linearFace (G:=G) (x,k.plaq) P=0 from he' ..,constant_will (R:=ℤ) A,map_zero,map_zero];simp
  rw [brace_value, secondary, show spectra S z (A ∘ Prod.snd)=0 from hh,shut,zero_add]
  unfold P at ht; rw [reveal h]; simp_rw [accent,ht]; exact congr_arg (fun x:G.Color=>(x p.2:ℂ)) (traced h S σ p.1 (fun p=>G.ad (A (six p)) (A (endr p))) he)

-- degree exactly and linear kernel weights; necessary for highest component projections
lemma production (u:RG.Slot)(x:Cover)(t:ℝ): take2 u x (t • A)= t^2 • take2 u x A:=by
  have ht(f: Face ℤ): acc f (t • A) = t^2 • acc f A:=by
    rw [Outline.plays,Outline.plays,Outline.witness,Outline.witness]; simp only [Finsupp.linearCombination_apply, Finsupp.sum, Pi.smul_apply, map_smul,LinearMap.smul_apply,Finset.smul_sum,smul_smul]; refine Finset.sum_congr rfl fun i _=>?_ ; congr 1; ring
  simp only [take2,roundTrip,Drift.conjugate,native,face_c, face_a,trip_a,map_zero, add_zero,map_smul, ht, LinearMap.smul_apply, smul_add]; rw [smul_smul,← pow_two]
lemma second_fee (t:ℝ)(x:Cover): secondary S x (t • A)=t^2 • secondary S x A:=by simp_rw [secondary,map_smul,show accent S x (t • A)= t^2 • accent S x A from funext fun i=> production A (S.looks i) x t, smul_add,show curvature2 S (t • _)= _ from bans S t (spectra S x A),map_smul]
lemma brace_degree (z:Cover): Hom (brace S σ p z) 2:=glow fun t A=>by rw [brace_value,brace_value,second_fee,map_smul]; simp only [PiLp.smul_apply, smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_pow]
end YM.XSpace.Chiral
