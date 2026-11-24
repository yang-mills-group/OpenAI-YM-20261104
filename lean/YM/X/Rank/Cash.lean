import YM.X.Rank.Stroke
/-!
# If an observable expectation with quadratic insertions vanishes identically,
can test arbitrary *flavor-only* choices at the two probed color-contracted positions
(or at the same position) in its polynomial. Statement operates with the full product.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Rad
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {s : Finset Stroke} (c : G.ColorIndex) {P : Canvas G}

abbrev glimpse (c:G.ColorIndex)(a:Scout) := fun z:Stroke=> (pay c a z:ℂ)
lemma layer (s : Finset Stroke) (L : (Stroke→ℂ) →ₗ[ℂ] ℂ) (h:∀ a:Scout,a.1∉ S → L (glimpse c a)=0) (hp:∀ y:Stroke→ℂ,EqOn y 0 s → L y=0) : L=0 := by
  have ha (f : Stroke→ℂ) : L f = ∑ k∈s,L (Pi.single k 1)* f k:= by
    let a:=∑ k∈s,f k • Pi.single k 1
    have he : L (f-a)=0:= by
       apply hp; intro z hz; unfold a; simp [Finset.sum_apply,Pi.single_apply,show z∈s from hz]
    rw [map_sub, sub_eq_zero] at he; rw [he,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul]; exact mul_comm ..
  let W i:= L (Pi.single i 1)
  have hh w (hw:w.1∉S) : ∑ i∈s, W i*glimpse c w i=0 := by rw [← show L (glimpse c w)= _ from ha _,h _ hw]
  have ht i (hi:i∈s) : W i=0:= by
    apply Complex.ext
    · exact controls c s (fun k=>(W k).re) S (fun w hw=>by simpa [glimpse,Complex.mul_re] using congr_arg Complex.re (hh w hw)) _ hi
    exact controls c s (fun k=>(W k).im) S (fun w hw=>by simpa [glimpse,Complex.mul_im] using congr_arg Complex.im (hh w hw)) _ hi
  exact LinearMap.ext fun f=> (ha f).trans (Finset.sum_eq_zero (fun i hi=> by rw [show L _= _ from ht i hi,mul_comm, mul_zero])) -- edit

/-- Two slits, color-paired, not constrained to two separate sites. -/
def Lap {V I : Type*} [Fintype I] (x y : V → ℂ) : Module.End ℂ (poly (V×I)) :=
    ∑ i:I,(slit (fun k:V×I=>if k.2=i then x k.1 else 0)).toLinearMap.comp (slit (fun k:V×I=>if k.2=i then y k.1 else 0)).toLinearMap
lemma lap_at (x y:Stroke→ℂ)(p: Canvas G): Lap x y p= ∑ i:G.ColorIndex,slit (dip x i) (slit (dip y i) p):=by
  unfold Lap; rw [LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i hi=> ?_; dsimp; unfold dip; congr!
lemma lap_sym {V I : Type*}[Fintype I](x y:V→ℂ) : Lap (I:=I) x y=Lap y x:=by
  unfold Lap; exact Finset.sum_congr rfl fun i (_:i∈Finset.univ)=> LinearMap.ext fun _=> slit_slit ..
lemma lap_pt (a b:Scout)(p:Canvas G): E c (patch a b*p)= Fintype.card G.ColorIndex * hot c b a * E c p + E c (Lap (glimpse c a) (glimpse c b) p):=by
  rw [lap_at]; unfold patch; simp_rw [Finset.sum_mul,_root_.map_sum, mul_assoc,leg_reads,Derivation.leibniz,slit_cost]
  simp only [↓reduceIte, smul_eq_mul]; simp_rw [_root_.map_add, mul_comm p, C_mul', map_smul, smul_eq_mul, leg_reads, Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; conv => lhs; lhs; arg 2; intro i; rhs; rw [slit_slit]; -- edit
  simp only [cost,glimpse]; ring
lemma Lap_money (y : Stroke→ℂ) (c : G.ColorIndex) (p: Canvas G): ∃ L : (Stroke→ℂ) →ₗ[ℂ] ℂ, ∀ w, E c (Lap w y p)=L w:=by -- remove x
  let f w:= E c (Lap w y p)
  refine ⟨⟨⟨f,?_⟩,?_⟩,fun w=>rfl⟩
  · intro u v; unfold f; simp_rw [lap_at]; rw [show dip (u+v)=(fun i:G.ColorIndex=>dip u i+dip v i) from ?_] -- use simp_rw
    · simp_rw [slit_linear, Finset.sum_add_distrib,map_add]
    funext i j; unfold dip; split_ifs <;> simp_all
  intro k w; change f (k • w)=k • f w; unfold f; simp_rw [lap_at]; rw [show dip (k • w)=(fun i:G.ColorIndex=>k • dip w i) from ?_]
  swap; · funext i j; by_cases h:j.2=i<;> simp [dip,h]
  simp only [slit_smul, ← Finset.smul_sum,map_smul]
lemma restrict_lap (p:Canvas G)(h:Silent c p S) : E c p=0:= by simpa [clothe] using h [] (by simp [adm,loci]) -- remove
lemma Lap_zero (q r:Stroke→ℂ) (h:Silent c P S)(hp:Fits (S:Set E4) P): E c (Lap q r P)=0:= by
  let s:= P.vars.image Prod.fst
  have hy (q r:Stroke→ℂ)(hr:EqOn q 0 s): Lap q r P=0:= by
    rw [lap_sym, lap_at]; refine Finset.sum_eq_zero fun i hi=>?_; rw [slit_dark q i (p:=P) (fun j hj=> hr (Finset.mem_image_of_mem _ hj)),map_zero]
  have ht (S' : Finset E4) (x:Stroke→ℂ)(H:∀ a:Scout,a.1∉S' → E c (Lap (glimpse c a) x P)=0)(p:Stroke→ℂ): E c (Lap p x P)=0:= by
    obtain ⟨L,hL⟩:= Lap_money x c P
    rw [hL, show L=0 from layer c s L (fun a h=> (hL _).symm.trans (H _ h)) (fun y hh=> (hL y).symm.trans (by rw [hy y x hh,map_zero])),LinearMap.zero_apply]
  apply ht S r; intro a ha; rw [lap_sym]
  apply ht (insert a.1 S) (glimpse c a)
  intro b hb; obtain ⟨hb,hV⟩:= (show b.1 ≠ a.1 ∧ b.1∉S from by simpa using hb)
  have hh:=(lap_pt c b a P).symm.trans (pair_reads c hp h hV ha hb b.2 a.2)
  simpa [restrict_lap c P h] using hh
end YM.PositionX.Rank
