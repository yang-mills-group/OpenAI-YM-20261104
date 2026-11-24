import YM.FVA2.Generator.Render
import YM.RG12.Strike.Film
/-!
# Taylor projection helpers in the scale-generator calculation

Need these for the $\chi$ annulus/Taylor projection, not making Taylor
assertions on position correlators at coincidences. `chains` and `dusty`
deal with the external `screen` on the terms we will use. See `Cry`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Exterior
open Function Set Filter XSpace Center XSpace.Litter XSpace.Scale XSpace.Trace XSpace.Lows RG12.Strike Maxwell Further.FreeCovariance.KP
open scoped Topology BigOperators ContDiff Classical
lemma bar_eq (i:Axis) : bar i=basis i :=by simp [bar,basis, EuclideanSpace.basisFun_apply]
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}{n m d:ℕ}
section silk
variable (v:F →L[ℝ] ℂ) {f:E4→F} {S:Set E4}{x:E4} (hs:IsOpen S)(h:∀ x∈S, ContDiffAt ℝ ω f x)(hx:x∈S)
include h in
lemma veiled : silk S (v ∘ f) := fun t ht=> v.contDiff.contDiffAt.comp t (h t ht) -- include
include hs hx in
lemma tuner {f:E4→ℂ}(h: silk S f)(hf:ContDiffAt ℝ ω f x)(L: List Axis): barrage f L x= ride L f x:=by
    let w:=L.get; have hu: List.ofFn w=L:=List.ofFn_get L
    have hx := read_tape hs h hx L.length w; rw [hu] at hx; rw [hx, XSpace.Compat.KP.reports L (hf.of_le le_top) ]; exact congr_arg _ (funext fun i=> (bar_eq _).trans (XSpace.Compat.KP.cyclists_at ..).symm )
include h hs hx
lemma retrieve (L:List Axis): v (ride L f x) = barrage (v ∘ f) L x:=by
    rw [tuner hs hx (veiled v h) (veiled v h x hx)] -- args order
    obtain he:=h x hx; rw [XSpace.Compat.KP.reports L (he.of_le le_top), XSpace.Compat.KP.reports L ((veiled v h x hx).of_le le_top),v.iteratedFDeriv_comp_left he le_top]; rfl
end silk
-- Type of true pointwise polynomial along rays from zero; get Strike moments by Taylor
-- identity along that ray. No assumed homogeneity of charged. Closure under products earns K1.
structure Mode (n:ℕ)(f:E4→ℂ): Prop where
    jet : silk univ f
    power (t:ℝ)(x:E4): f (t • x)=(t:ℂ)^n * f x
abbrev τ (n:ℕ):ℂ:=(↑(n.factorial):ℂ)⁻¹
namespace Mode
variable {f g:E4→ℂ}
lemma mul (p:Mode n f)(q:Mode m g): Mode (n+m) (f*g):=⟨fun y _ => (p.jet y trivial).mul (q.jet y trivial), fun t x=> by simp only [Pi.mul_apply,p.power,q.power,pow_add]; ring⟩
lemma paid (p:Mode n f)(x:E4): f x=τ n*sep n (fun l=>barrage f l 0) x :=by
    change f x=fresco n f 0 x
    rw [fern isOpen_univ p.jet (Set.mem_univ _)]
    change f x=τ n * iteratedDeriv n (fun t:ℝ=> f (t•x+0)) 0; have hv(t:ℝ): f (t • x+0)= t^n • f x:= by rw [add_zero,p.power,Complex.real_smul]; push_cast; rfl
    simp_rw [hv]; rw [iteratedDeriv_smul_const (by fun_prop: ContDiffAt ℝ n (fun t:ℝ=> t^n) 0),iteratedDeriv_fun_pow_zero, if_pos rfl,Complex.real_smul,Complex.ofReal_natCast,← mul_assoc]; rw [τ,inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n),one_mul]
lemma law (p:Mode n f): VectorLaw f (-(↑n:ℤ)):= fun x _ t _=> by rw [p.power,neg_neg,zpow_natCast]
lemma center (p:Mode n f)(h:0<n): f 0=0:=by simpa only [zero_smul,Complex.ofReal_zero,zero_pow h.ne',zero_mul] using p.power 0 (0:E4)
end Mode

variable (v:F →L[ℝ] ℂ)
lemma rendition {i:Axis}(B:Stamp (n+1) F): hit i (v ∘ motifValue B) = v ∘ motifValue (dip i B):=funext fun y=> (along _ ((v.contDiff.comp (Tensor.diag_smooth B.val ω)).contDiffAt.differentiableAt (by decide))).trans (by
   rw [bar_eq]; change grad i (v ∘ motifValue B) y=_; rw [Maxwell.grad_linear v (show ContDiffAt ℝ ∞ (motifValue B) y from (Tensor.diag_smooth B.val ∞).contDiffAt),climbs]; rfl)
lemma graded (B:Stamp n F) : Mode n (v ∘ motifValue B):= ⟨veiled v (fun y _=> (Tensor.diag_smooth B.val ω).contDiffAt), fun t x=>by unfold Function.comp motifValue; rw [Tensor.homogeneous,map_smul,Complex.real_smul, Complex.ofReal_pow]⟩
lemma laps (u:List Axis)(B:Stamp m F)(h:n+u.length=m): Mode n (barrage (v ∘ motifValue B) u):= by induction u using List.reverseRecOn generalizing m with
    | nil=> simp only [List.length_nil,Nat.add_zero] at h; subst n; exact graded v B
    | append_singleton l i ih=> cases m with
         | zero => simp at h
         | succ m => rw [show barrage (v ∘ motifValue B) (l++[i])= _ from funext fun x=>barrage_append (v ∘ motifValue B) l [i] x, show barrage (v ∘ motifValue B) [i]=_ from rendition (i:=i) v B]; apply ih; simpa [← add_assoc] using h
lemma late (u:List Axis)(B:Stamp m F)(h:m < u.length): barrage (v ∘ motifValue B) u=0:=by induction u using List.reverseRecOn generalizing m with
    | nil=> simp at h
    | append_singleton l i ih=> cases m with
         | zero=>
            have he: motifValue B=fun _=> motifValue B 0:=funext fun x=> congr_arg B.val ( Subsingleton.elim .. )
            rw [show barrage (v ∘ motifValue B) (l++[i])= _ from funext fun x=>barrage_append (v ∘ motifValue B) l [i] x,he]; change barrage _ _=0
            rw [show barrage (v ∘ (fun _:E4=> motifValue B 0)) [i]=0 from funext fun x=> by apply deriv_const]; exact funext fun x=> barrage_zero ..
         | succ m=> rw [show barrage (v ∘ motifValue B) (l++[i])= _ from funext fun x=>barrage_append (v ∘ motifValue B) l [i] x, show barrage (v ∘ motifValue B) [i]=_ from rendition (i:=i) v B]; apply ih; simpa using h

def paint (c:G.ColorIndex): G.Color→L[ℝ] ℂ:= Complex.ofRealCLM.comp (EuclideanSpace.proj c)
lemma dyes (c:G.ColorIndex)(u:G.Color): paint c u=(u c:ℂ):=rfl
def panel (B:Hat G d) (m:Fin (d+1))(j:Axis)(c:G.ColorIndex) : E4→ℂ:= paint c ∘ motifValue ((B m).val j)
def screen (B:Hat G d)(v:Bond G)(m:Fin (d+1)):= barrage (panel B m v.j v.color) v.k
lemma chains (B:Hat G d)(v:Bond G)(p:Fin (d+1))(h:v.k.length≤p.val): Mode (p.val-v.k.length) (screen B v p):=laps _ _ _ (by omega)
lemma dusty (B:Hat G d)(v:Bond G)(p:Fin (d+1))(h:p.val < v.k.length): screen B v p=0:=late _ _ _ h
lemma pigment (B:Hat G d)(v:Bond G)(m:Fin (d+1))(x:E4): screen B v m x=paint v.color (ride v.k (motifValue ((B m).val v.j)) x):= (retrieve (x:=x) (paint v.color) isOpen_univ (fun _ _=> (Tensor.diag_smooth _ ω).contDiffAt) (Set.mem_univ _) v.k).symm
end YM.FVA2.Generator.Exterior
