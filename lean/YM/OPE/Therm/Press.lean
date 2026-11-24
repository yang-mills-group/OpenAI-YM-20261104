import YM.OPE.Therm.Mortgage
/-!
# Fresh interior bank, real envelopes

`press X f` integrating above independent Haar, restoring exterior. No claims of
locality of the density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.House
open Function Set Filter RG Lattice Wilson MeasureTheory Cells
open scoped BigOperators Classical Topology
section
variable {V F:Type*} [MeasurableSpace V] [MeasurableSpace F]{ι: Type*}
lemma branch (X:Finset ι) (A:ι→V→ℝ)(h:∀ i∈X, Envelope (A i)): Envelope (fun v=> ∏ i∈X,A i v):=by
   induction X using Finset.induction_on with
   | empty => simpa only [Finset.prod_empty] using Envelope.const (V:=V) 1
   | insert i X hi ih=> simp only [Finset.prod_insert hi]; exact Envelope.mul (h i (Finset.mem_insert_self ..)) (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma enclosed {f: F→ℝ}{g: V→ F}(h:Envelope f)(hf: Measurable g) : Envelope (fun x=> f (g x)):= by obtain ⟨C,H⟩:=h.cost; exact ⟨h.meas.comp hf,C,fun x=> H (g x)⟩
end
variable {n:Side} {G:Gauge}{F : Sort*}
variable {U V : Config G n} {X Y: Finset (Edge (Site n))} {P : Set (Site n)}
local notation "𝒞" => Config G n
local notation "E" => Edge (Site n)
local notation "η" => prior G n
-- fence meaning
lemma fence_iff : Agrees P U V ↔ Set.EqOn U V (links P) := by
   constructor <;> intro h
   · intro x hx; exact h x (linn.mp hx).1 (linn.mp hx).2
   exact fun e h1 h2 => h (show e∈ links P from linn.mpr ⟨h1,h2⟩)
def fence (X:Finset E)(f:𝒞→F) := ∀ U V, EqOn U V X → f U=f V
lemma local_fence {F:Type*} {f:𝒞→F} : fence (links P) f ↔ LocalOn P f:=⟨fun h x y he=> h x y (fence_iff.mp he), fun h x y he=> h x y (fence_iff.mpr he)⟩
def stills (X:Finset E)(f:𝒞→F) := fence Xᶜ f
lemma sharing {f:𝒞→F}(h:fence X f) (he: X ⊆ Y) : fence Y f:=fun U V hu=> h U V (hu.mono (fun _ hi=> he hi))
lemma spares {f:𝒞→F}(h:fence X f)(he:Disjoint X Y) : stills Y f := sharing h fun _ hx=> Finset.mem_compl.mpr (Finset.disjoint_left.mp he hx)
def meld (X:Finset E)(V U:𝒞):𝒞:=fun e=> if e∈X then V e else U e
@[fun_prop] lemma meld_meas {F:Type*}[MeasurableSpace F]{x y:F→𝒞}(hx:Measurable x)(hy:Measurable y): Measurable (fun p=>meld X (x p) (y p)):= by
   apply measurable_pi_lambda; intro i; unfold meld; split; exact (measurable_pi_apply i).comp hx; exact (measurable_pi_apply i).comp hy
lemma meld_on (X:Finset E)(V U:𝒞): EqOn (meld X V U) V X:= fun i he=> if_pos he
lemma meld_off (X:Finset E)(V U:𝒞): EqOn (meld X V U) U (↑(Xᶜ:Finset E)):=fun i he=> if_neg (Finset.mem_compl.mp he)
lemma warms {f:𝒞→F} (h:stills X f) (U V:𝒞) : f (meld X V U)= f U:= h _ _ (meld_off ..)
def press (X:Finset E)(f:𝒞→ℝ)(U:𝒞) := ∫ V,f (meld X V U)∂η
lemma dormant (X:Finset E)(f:𝒞→ℝ): stills X (press X f):=by
   intro U V hp; refine integral_congr_ae (Eventually.of_forall fun u=> congr_arg f (funext fun i=>?_)); unfold meld; split; rfl; rename_i hi; exact hp (show i∈ (↑(Xᶜ:Finset E):Set _) from Finset.mem_compl.mpr hi)
lemma held_mass (X:Finset E){f:𝒞→ℝ}(h:Envelope f) :Envelope (press X f):=by
   obtain ⟨C,H⟩ := h.cost; have ht:Envelope (fun p:𝒞×𝒞=>f (meld X p.2 p.1)):= enclosed h (meld_meas measurable_snd measurable_fst)
   exact ⟨ht.meas.stronglyMeasurable.integral_prod_right'.measurable,C,fun U=> by simpa only [press,measureReal_univ_eq_one,mul_one,one_mul] using norm_integral_le_of_norm_le_const (μ:=η) (Eventually.of_forall fun x=>H (meld X x U)) ⟩
lemma press_add (X:Finset E){f g:𝒞→ℝ}(h:Envelope f)(he:Envelope g)(U:𝒞) : press X (fun U'=> f U'+g U') U= press X f U+ press X g U:= integral_add ((enclosed h (meld_meas (X:=X) (measurable_id (α:=𝒞)) (show Measurable (fun _ :𝒞=> U) from measurable_const))).integrable _) ((enclosed he (meld_meas measurable_id measurable_const)).integrable _)
lemma press_mono (X:Finset E){f g:𝒞→ℝ}(h:Envelope f)(he:Envelope g)(hp:f≤g) (U:𝒞): press X f U ≤ press X g U := integral_mono ((enclosed h (meld_meas measurable_id measurable_const)).integrable _) ((enclosed he (meld_meas measurable_id measurable_const)).integrable _) (fun x=>hp (meld X x U))
lemma pressmul {f:𝒞→ℝ}(g:𝒞→ℝ)(h:stills X f)(U:𝒞): press X (fun x=> g x*f x) U= press X g U * f U:=by unfold press; simp_rw [warms h, integral_mul_const]
lemma pressmulL {f:𝒞→ℝ}(g:𝒞→ℝ)(h:stills X f)(U:𝒞): press X (fun x=> f x*g x) U= f U*press X g U:=by unfold press; simp_rw [warms h, integral_const_mul]
lemma markSpaces {f:𝒞→ℝ}(h:stills X f)(U:𝒞): press X f U=f U:= by unfold press; simp_rw [warms h]; simp
lemma fresh (X:Finset E){f:𝒞→ℝ}(h:Envelope f) : (∫ U,press X f U∂η)=∫ U,f U∂η := by
   let H := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : E=> G.El) (·∈X)
   have he:= measurePreserving_piEquivPiSubtypeProd (fun _ : E=> G.probHaar) (·∈X)
   let r:= Measure.pi (fun _:Subtype (·∈X)=> G.probHaar); let s:=Measure.pi (fun _: Subtype (fun e=> e∉ X) => G.probHaar)
   have hm (x y u v): meld X (H.symm (x,y)) (H.symm (u,v))=H.symm (x,v):=by
      ext1 i; unfold H; change meld X ((Equiv.piEquivPiSubtypeProd (·∈X) (fun _=>G.El)).symm (x,y)) _ i = _; unfold meld; split_ifs with hi <;> simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply,hi]
   have ha (f:𝒞→ℝ)(h:Envelope f): (∫ U,f U∂η)=∫ x,∫ y,f (H.symm (y,x))∂r∂s:=by rw [← (show MeasurePreserving H.symm (r.prod s) η from (MeasurePreserving.symm H (by convert! he))).integral_comp H.symm.measurableEmbedding f]; exact integral_prod_symm _ ((enclosed h H.symm.measurable).integrable _)
   have hx (x y): press X f (H.symm (x,y))=∫ z, f (H.symm (z,y))∂r:=by
      unfold press; rw [ha (fun V=> f (meld X V (H.symm (x,y)))) (enclosed h (meld_meas measurable_id measurable_const))]
      simp only [hm]; simp [s]
   rw [ha _ (held_mass X h),ha f h]; simp_rw [hx]; simp [r]
lemma fresh_le (X:Finset E){f g:𝒞→ℝ}(h:Envelope f)(he:Envelope g)(hp: press X f ≤ press X g):(∫ U,f U∂η)≤∫ U,g U∂η:=by rw [← fresh X h, ← fresh X he]; exact integral_mono ((held_mass X h).integrable _) ((held_mass X he).integrable _) hp
lemma meld_pull (s:Signed)(x:Site n)(h:∀ i:Edge (Site n), i∈X ↔ twist s x i ∈Y) (V U:𝒞): pull s x (meld Y V U) = meld X (pull s x V) (pull s x U):= by
   ext1 i; simp_rw [WardBin.Wheels.pull_by]; unfold meld; simp_rw [WardBin.Wheels.pull_by]; split_ifs <;> first | rfl | (specialize h i;change _ ↔ sendEdge s x i∈Y at h; tauto)
lemma press_turn (s:Signed)(x:Site n)(h:∀ i:Edge (Site n), i∈X ↔ twist s x i∈Y) (f:𝒞→ℝ)(U:𝒞): press X f (pull s x U) = press Y (fun U=> f (pull s x U)) U:=by
   unfold press; simp_rw [meld_pull s x h]; exact Eq.symm ((prior_pull s x).integral_comp (WardBin.Wheels.embedding_pull s x) (fun V=> f (meld X V (pull s x U))))
end YM.OPE.Therm.House
