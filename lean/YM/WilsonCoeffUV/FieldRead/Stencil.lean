import YM.WilsonCoeffUV.FieldRead.Alphabet
import YM.Planned.PRIMARY_INTEGRAL_295.Pearl
/-!
# Actual local stencil top. The graph origins, not transfer's normalized x.
Root derivative at cover o, halo Fourier path convention independent.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Set Matrix Laurent Lattice RG Exterior Precision Next.Free Gauge Power
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider Fountain
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m n p e:ℕ}{A C s t :ℝ}
variable {F:Frame G h} (T:SectionData F)

abbrev Toe:= Spot T.stencil × G.ColorIndex
def vixen: Lawn (Toe T) ≃L[ℝ] Dev T.stencil G:= LinearEquiv.toContinuousLinearEquiv {
       toFun x i:= coatC G (fun j=> x (i,j))
       invFun x p:= (x p.1) p.2
       left_inv _:=rfl
       right_inv _:=rfl
       map_add' _ _:=rfl
       map_smul' _ _:=rfl }
lemma nav (p:Toe T): (vixen T) (pebble p)= Pi.single p.1 (coatC G (Pi.single p.2 1)):= by
   ext i j; change pebble p (i,j)=_
   by_cases h:i=p.1
   · subst i; rw [Pi.single_eq_same]; simp [pebble,Pi.single_apply]; change _= (Pi.single (M:=fun _=>ℝ) p.2 1 j); simp [Pi.single_apply,eq_comm]; cases p; simp [eq_comm]
   rw [Pi.single_eq_of_ne h]; change _=0; simp [pebble,Pi.single_apply]; intro he; exact h (congr_arg Prod.fst he)

def collar (i:F.Index)(x:Lawn (Toe T)):= (Place.column T i (vixen T x)).re
lemma follicle (i:F.Index): Blue.Green (collar T i):= Complex.reCLM.contDiff.contDiffAt.comp (0:Lawn (Toe T)) ((Place.column_smooth ..).contDiffAt.comp _ (vixen T).toContinuousLinearMap.contDiff.contDiffAt)
lemma wool (i:F.Index)(he:Bid.pop T)(u:r<(F.grades i).2): rye (collar T i) r=0:=by
   funext v; unfold rye; let g:= (vixen T).toContinuousLinearMap; let L:= Complex.reCLM
   change (r.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ r (L ∘ (Place.column T i ∘ g)) 0 _= _
   rw [L.iteratedFDeriv_comp_left ((Place.column_smooth T i).contDiffAt.comp _ g.contDiff.contDiffAt) (by simp), Next.Foundations.jets_linear _ ((Place.column_smooth T i).contDiffAt.of_le le_top), radials_vanish T he i r u]; exact (smul_zero ..)
lemma shawl (i:F.Index)(H:Hol G)(d:T.Sound H)(x:Lawn (Toe T)): (collar T i x:ℂ)=T.evaluate (Pi.single i 1) (pore (vixen T x)):=by
   refine Complex.ext rfl ?_; let v := Pi.single (M:=fun _=>ℂ) i 1
   have he : star (T.evaluate v (pore (vixen T x)))=T.evaluate v (pore (vixen T x)):= by rw [←d.ordinary_real]; congr 1; unfold v; ext j; simp [Pi.single_apply]
   have ht:=congr_arg Complex.im he
   set k:= T.evaluate v (pore (vixen T x)); change -k.im=k.im at ht; rw [Complex.ofReal_im]; change 0=k.im; linarith

def dance (p:Toe T): YForest G:= stone (placeEdge p.1) p.2
lemma dance_inj: Injective (dance T):=by
    rintro ⟨⟨⟨⟨p,hp⟩,i⟩,hi⟩,q⟩ ⟨⟨⟨⟨x,hx⟩,j⟩,hj⟩,v⟩ h
    have he:= congr_arg feather h; unfold dance at he; simp_rw [feather_at] at he
    have hu := show (p,i)=(x,j) from he; have ht :q=v:= congr_arg (fun x:YForest G=>x.2.2) h; cases Prod.mk.inj hu; subst_vars; rfl

def floatA (T:SectionData F) (z:F.Index)(r:ℕ): ChamberTen G ℝ r:= fade (spear (dance T)) (shine (rye (collar T z) r)) r
lemma smoothFloat (z:F.Index)(r:ℕ): Blue.Smooth (floatA T z r):= fade_pure (shine_pure (rye_sym (follicle T z) r)) (spear (dance T)) r
lemma apt (z:F.Index)(u:Fin r→Toe T): floatA T z r (dance T ∘ u)=rye (collar T z) r u:=by
   unfold floatA fade; rw [Finset.sum_eq_single u]
   · simp only [shine_lit, spear, Matrix.of_apply, Function.comp_apply]; simp
   · intro j _ h; obtain ⟨i,hi⟩:=Function.ne_iff.mp h; rw [Finset.prod_eq_zero (Finset.mem_univ i), zero_smul]; exact if_neg (fun e=>hi ((dance_inj T e).symm))
   simp

lemma treasury (z:F.Index)(x:Fin r→ YForest G)(h:x ∉ Set.range (fun u:Fin r→Toe T=> dance T ∘ u)): floatA T z r x=0:=by
   unfold floatA fade; apply Finset.sum_eq_zero; intro p _
   obtain ⟨i,hi⟩:= Function.ne_iff.mp (show dance T ∘ p≠x from fun hx=>h ⟨_,hx⟩)
   rw [Finset.prod_eq_zero (Finset.mem_univ i),zero_smul]; rw [spear,Matrix.of_apply,if_neg]; exact hi.symm
lemma aca (z:F.Index)(hp:r<(F.grades z).2)(u:Bid.pop T): floatA T z r=0:=by
    funext; rw [floatA, wool T z u hp]; unfold fade; simp_rw [shine_lit]; simp
lemma paidAnn (z:F.Index)(r:ℕ)(s:ℝ):∃ C:ℝ,Twig 0 s C (floatA T z r):=by
   let f:=floatA T z r
   let M (x:Fin r→ YForest G):= port_d 0 x
   let W (x:Fin r→ YForest G):= Real.exp (s*M x)
   let V:=∑ u:Fin r→ Toe T, ‖f (dance T ∘ u)‖* W (dance T ∘ u)
   have hv:0≤V:= Finset.sum_nonneg fun i _=> by unfold W; positivity
   refine ⟨V,hv,fun x=>?_⟩
   change ‖f x‖≤ _; rw [neg_mul,Real.exp_neg,←div_eq_mul_inv]; apply (le_div_iff₀ (by positivity)).mpr; by_cases h:x∈Set.range (fun u:Fin r→ Toe T=>dance T ∘ u)
   · obtain ⟨i,rfl⟩:=h; exact Finset.single_le_sum (f:=fun u=> ‖f (dance T ∘ u)‖*W (dance T ∘ u)) (fun i _=>by unfold W; positivity) (Finset.mem_univ i)
   rw [show f x=0 from treasury T z x h,norm_zero,zero_mul]; exact hv

variable (w:h < D)
def prizeBloom (u:Alma F)(c:Volume D):ℝ:=
    let v := (⟨⟨_,Nat.lt_succ_of_le ((notar F u).property.trans w.le)⟩,knurl (notar F u)⟩:Knob D)
    claim D v zeroC c

def jewelBloom (v:Alma F):Vote D:= claim D ⟨⟨_,Nat.lt_succ_of_le ((notar F v).property.trans w.le)⟩,knurl (notar F v)⟩ zeroC
lemma packBloom (v u:Alma F): jewelBloom w v (brow F u D)=if notar F v=notar F u then 1 else 0:=by
    change crease (testa D _) (knurl _) 0= _; rw [coinage,knurls]; by_cases ht:notar F v=notar F u; · rw [ht]; simp
    rw [if_neg ht, if_neg (fun h=>ht (Subtype.ext h.symm))]
def carte (v:Alma F)(r:ℕ): ChamberTen G (Vote D) r := fun x=> floatA T (sheet F v) r x • jewelBloom w v
def anthem (v:Alma F) : Single G D:= fun e=> shine (carte T w v (valence F v+e))
lemma shrine (v:Alma F): shellK (valence F v) (anthem T w v):=fun e j t=> shine_dark (by omega)
lemma wise (v:Alma F)(e:ℕ): Pure (anthem T w v e) := shine_pure (fun i s=> congr_arg (· • jewelBloom w v) (smoothFloat T _ _ i s))
lemma covered (i:Alma F)(e r:ℕ)(s:ℝ): ∃ M:ℝ, Twig 0 s M (anthem T w i e r):=by
    unfold anthem; by_cases hv:valence F i+e=r; · subst r; rw [shine_lit]; obtain ⟨C,h⟩:= paidAnn T (sheet F i) (valence F i+e) s; refine ⟨C*‖jewelBloom w i‖,mul_nonneg h.1 (norm_nonneg _), fun j=>?_⟩; unfold carte; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (h.2 j) (norm_nonneg _)).trans_eq (by ring)
    rw [shine_dark hv]; exact ⟨_,Twig.zero⟩
end YM.WilsonCoeffUV.Cosmos
