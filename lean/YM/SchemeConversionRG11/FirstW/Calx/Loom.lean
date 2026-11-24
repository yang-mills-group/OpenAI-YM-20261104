import YM.SchemeConversionRG11.FirstW.Calx.Neck
/-! Differential open site limits. Curtain probes. Scaling *of* functions vs integrands indexed on Cover. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent
open scoped BigOperators Classical ContDiff
variable {n : Side}
variable {T:Itinerary} {E F P X:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup P][NormedSpace ℝ P]
variable {G:Gauge} {K:Set E4}{f g:ℕ → Cover → E}{p:ℕ → Cover}{a b c v:ℤ}{x:E4}
abbrev ped (T:Itinerary)(a:ℤ)(f:ℕ → Cover→ E)(i:ℕ)(x:Cover):= T.gap i ^ a • f i x
lemma harbor_tread (p:ℕ → Cover)(h:Harbor T p x)(v:Cover): Harbor T (fun j=> p j+v) x:=by unfold Harbor Moss; simp_rw [inc_add]; simpa only [add_zero] using Tendsto.add h (inc_const T v)
-- Loom existential (don't silently substitute per-sequence limits)
def Melody (T:Itinerary)(K:Set E4)(a:ℤ)(f:ℕ → Cover→ E):= ∃ g:E4→ E,Loom T K (ped T a f) g
lemma Melody.add (h:Melody T K a f)(hp:Melody T K a g) : Melody T K a (fun i x=> f i x+g i x):=by obtain ⟨A,h⟩:=h; obtain ⟨B,hp⟩:=hp; exact ⟨A+B,fun σ hs v hv p he=>by simp only [ped,smul_add]; exact (h σ hs v hv p he).add (hp σ hs v hv p he)⟩
lemma Melody.sub (h:Melody T K a f)(hp:Melody T K a g) : Melody T K a (fun i x=> f i x-g i x):=by obtain ⟨A,h⟩:=h; obtain ⟨B,hp⟩:=hp; exact ⟨A-B,fun σ hs v hv p he=>by simp only [ped,smul_sub]; exact (h σ hs v hv p he).sub (hp σ hs v hv p he)⟩
lemma Melody.zero : Melody T K a (fun _ _ => (0:E)):= ⟨0, fun σ hs v hv p H=>by simp⟩
lemma Melody.drift (h:Melody T K a f) (x:Cover) : Melody T K a (fun i v=> f i (v+x)):=by obtain ⟨A,h⟩:=h; exact ⟨A,fun σ hs v hv p he=> h σ hs v hv _ (harbor_tread p he x)⟩
lemma Melody.linked {k:ℕ → Cover→ F} (hf: Melody T K a f)(h: Melody T K b k)(L : E→L[ℝ] F→L[ℝ] P): Melody T K (a+b) (fun i x=>L (f i x) (k i x)):= by
 obtain ⟨A,hA⟩:=hf; obtain ⟨B,hB⟩:=h
 refine ⟨fun x=> L (A x) (B x), fun σ hs v hv p hp=>?_⟩
 let g (x:E × F): P := L x.1 x.2
 have hg:Continuous g := (L.continuous.comp continuous_fst).clm_apply continuous_snd
 have ht:= hg.continuousAt.tendsto.comp ((hA σ hs v hv p hp).prodMk_nhds (hB σ hs v hv p hp)); apply ht.congr; intro i; dsimp only [g,comp_apply,ped]; simp [map_smul, smul_smul,zpow_add₀ (T.positive (σ i)).ne',mul_comm]
lemma Melody.fixed (hf:Melody T K a f)(c:ℝ): Melody T K a (fun i x=> c • f i x):=by
 obtain ⟨A,h⟩:=hf; refine ⟨c • A,fun σ hs v hv p hp=>?_⟩; exact (Tendsto.const_smul (h σ hs v hv p hp) c).congr fun i=> smul_comm ..
lemma Melody.sum {f:X→ℕ → Cover→ E}(s:Finset X) (h:∀ i∈s, Melody T K a (f i)): Melody T K a (fun i x=>∑ j∈s,f j i x):=by
 induction s using Finset.induction with|empty=>simp only [Finset.sum_empty]; exact Melody.zero|insert c s hc ih=>simp only [Finset.sum_insert hc]; exact (h c (Finset.mem_insert_self ..)).add (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
-- potentials have value and lap stride asymptotics; include Watt
structure Deaf (T:Itinerary)(S:Set E4)(a:ℤ)(f:ℕ → Field4 G): Prop where
 cap(i:Axis): Melody T S a (fun j x=> f j (x,i))
 loft (i j:Axis): Melody T S (a-1) (fun k x=> up j (field4 i (f k)) x)
-- translate Score statement to cover
lemma light_tape (t:Deck.Who G 6) (T:Itinerary) (d:Axis) (D:List Axis) (k:ℤ) (hk:k= -(↑(fee t+1+D.length:ℕ):ℤ)) : Loom T {x:E4|x≠0} (ped T k (fun i x=>combine D (field4 d (tin G (T.period i) t)) x)) (tongs t.val d D) := by
 intro σ hs v hv p hp
 have H:= stream t.val T d D σ hs v hv (fun j=>wrap (T.period (σ j)) (p j)) (sails_wrap (T:=Rig.path T σ hs) hp)
 have eq {n:Side} (D:List Axis) (f:Site n→ G.Color)(x:Cover): combine D f (wrap n x)=combine D (f ∘ wrap n) x:= by induction D generalizing x with | nil=> rfl | cons i D ih=>simp only [combine,up, ←ih,map_add,wrap_step]
 apply H.congr; intro i
 let h:=T.gap (σ i); let N:=T.period (σ i); let f:=field4 d (tin G N t)
 let g : Site N → G.Color := fun x=> canal t.val 0 (x,d);
 have he : knot T t.val d (σ i)= h⁻¹ • ( (h^fee t)⁻¹ • g):= funext fun x=>by simp only [knot,g,river,Pi.smul_apply];rfl
 have hr : f=g ∘ wrap N:= funext fun x=>by simp [f,g,tin,terms,N,field4]
 change (h^D.length)⁻¹ • combine D (knot T t.val d (σ i)) (wrap N (p i))=_; rw [he,combine_smul,combine_smul, Pi.smul_apply,Pi.smul_apply,eq,_root_.smul_smul,smul_smul,hk]; simp only [ped,zpow_neg,zpow_natCast,pow_add,pow_one,mul_inv,← hr]; apply congrArg (fun c:ℝ=> c • _); unfold h;ring
lemma lit_point (t:Deck.Who G 6) (T:Itinerary) (h:fee t=2) : Deaf T {x:E4|x≠0} (-3) (fun i=>tin G (T.period i) t) := by
 refine ⟨fun i=> ⟨_,light_tape t T i [] _ (by rw [h];rfl)⟩,fun i j=>⟨_,light_tape t T i [j] _ (by rw [h];rfl)⟩⟩
lemma figK (k:ℕ) (f:Cover→ E) (h:f∈ Loft E k) : Melody T univ (k:ℤ) (fun _=> f) := by
 refine ⟨dialP k f,fun σ hs v hv p hp=>?_⟩; simp only [ped,zpow_natCast]; exact cropped k f h _ _ _ (Rig.path T σ hs).cutoff hp
end YM.RG11.FirstW
