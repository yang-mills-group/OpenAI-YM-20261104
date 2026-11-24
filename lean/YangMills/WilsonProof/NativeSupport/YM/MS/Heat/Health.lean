import YM.MS.Heat.Health
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Park
import YM.MS.Heat.Build
/-!
# Joint of absolute heat length and any charts

Turning property of all coordinates even in bulk requires *smooth off Course*, not signed or exchange there if not preserved. Use param integral contours on compact domain. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Book Convolve Base
open Wire
open scoped Topology ContDiff
variable {E E' P A I:Type}[NormedAddCommGroup P][NormedSpace ℝ P][NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup E'][NormedSpace ℝ E'][Fintype A]
abbrev tagSmooth (E A P:Type):= List (A× (E→P))
def walk0 (l:tagSmooth E A P)(x:E): List (Mode A P):= l.map fun z=> (z.1,z.2 x)
def Trail (l: tagSmooth E A P): Prop:= ∀ i∈l, ContDiff ℝ ∞ i.2
variable {w:tagSmooth E A P} {f:E'→ E}
def easy (f: E'→ E) (w: tagSmooth E A P): tagSmooth E' A P:= w.map fun i=> (i.1,i.2∘ f)
namespace Trail
omit [Fintype A] in
lemma comp (h:Trail w)(hf:ContDiff ℝ ∞ f): Trail (easy f w):= by intro i hi; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hi; exact (h j hj).comp hf
omit [Fintype A][NormedAddCommGroup P][NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'][NormedSpace ℝ E'] in
lemma comp_walk (x:E'): walk0 (easy f w) x= walk0 w (f x):= by simp only [walk0,easy,List.map_map]; rfl
omit [Fintype A] in
lemma nil : Trail ([]:tagSmooth E A P):= by intro i h; simp at h
omit [Fintype A] in
lemma cons (h:Trail w)(i:A)(f:E→ P)(hv: ContDiff ℝ ∞ f) : Trail ((i,f)::w):= by intro a ha; obtain rfl|ht:= List.mem_cons.mp ha; exact hv; exact h a ht
omit [Fintype A] in
lemma splitL {f g: tagSmooth E A P}(h: Trail w)(hu:Split f g w): Trail f:= fun _ hi=>h _ ( (split_perm hu).mem_iff.mp (List.mem_append_left g hi)) -- namespace
omit [Fintype A] in
lemma splitR {f g: tagSmooth E A P}(h: Trail w)(hu:Split f g w): Trail g:= fun _ hi=> h _ ((split_perm hu).mem_iff.mp (List.mem_append_right f hi))
omit [Fintype A] in
lemma rest {i : Mode A (E→P)}(h:Trail (i::w)): Trail w:= fun a ha=> h a (List.mem_cons_of_mem i ha)
omit [Fintype A] in
lemma net0 (h:Trail w) : ContDiff ℝ ∞ (fun x:E=> net (walk0 w x)):= by
   induction w with | nil=> exact contDiff_const| cons a l ih=> simpa only [walk0,List.map_cons,net_cons] using (h a (by simp)).add (ih h.rest)
end Trail
-- point smooth definition at all charts

def TouchF (F: BF A P): Prop:= ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E], ∀ (f:E→ℝ)(w:tagSmooth E A P), Trail w→ ContDiff ℝ ∞ f→ ContDiff ℝ ∞ fun p=>F (f p) (walk0 w p)
variable {F H V : BF A P}{K:ℝ→ Flux A P ℂ} {p: Sector A}
-- times w no composition of ray hull
namespace TouchF
omit [Fintype A] in
lemma at_const (h:TouchF F)(f: E→ℝ)(l:List (Mode A P))(hx:ContDiff ℝ ∞ f): ContDiff ℝ ∞ (fun p=>F (f p) l):= by
    let L: tagSmooth E A P:= l.map fun i=> (i.1,fun _=>i.2); convert! h E f L ?_ hx using 1; · simp [walk0,L,Function.comp_def] -- lint
    intro a hz; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hz; exact contDiff_const
omit [Fintype A] in
lemma routine (h:TouchF F)(w:Wire A E P) (q:ℝ): ContDiff ℝ ∞ (fun p=> F q (sail w p)):= by
   let v := w.map fun i=> (i.1,(i.2 : E → P)); have he : ∀ q,walk0 v q=sail w q:= by simp only [v,walk0,sail,List.map_map]; exact fun _=> rfl
   simp_rw [← he]; refine h E (fun x=>q) _ ?_ contDiff_const; intro a ha; obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha; exact i.2.contDiff
omit [Fintype A] in
lemma zeros : TouchF (0: BF A P):= fun _ _ _ _ _ _ _=> contDiff_const
omit [Fintype A] in
lemma sum (J:Finset I){F:I→ BF A P}(h:∀ j∈J,TouchF (F j)): TouchF (fun t=>∑ i∈J,F i t):= by intro E _ _ f w he hx; simp_rw [Finset.sum_apply]; exact ContDiff.sum (fun i hi=> h i hi _ _ _ he hx)
omit [Fintype A] in
lemma add (h:TouchF F)(he:TouchF H): TouchF (F+H):= fun E _ _ f w hw ht=> (h E f w hw ht).add (he E f w hw ht)
omit [Fintype A] in
lemma scale (c:ℂ)(h:TouchF F): TouchF (fun t=>c • F t) := fun E _ _ f w hw ht=> ContDiff.mul contDiff_const (h E f w hw ht)
end TouchF

def flex (K:ℝ→ Flux A P ℂ): Prop:= ∀ a b, ContDiff ℝ ∞ fun y:ℝ×P=> K y.1 a b y.2
variable [MeasurableSpace P][BorelSpace P] [FiniteDimensional ℝ P]
variable (μ:Measure P) [IsFiniteMeasure μ]
omit [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ P] in
lemma flex_pays (H: TouchF F)(he:flex K)(q:E→ℝ)(hk:ContDiff ℝ ∞ q)(x:E→ P)(h:ContDiff ℝ ∞ x)(hw:Trail w): ContDiff ℝ ∞ (fun p=> trc (K (q p)) (x p) (F (q p)) (walk0 w p)):= by
   simp_rw [at_trc]; exact ContDiff.sum fun i _=> ContDiff.sum fun j _=> ((he i j).comp (hk.prodMk h)).mul (H E q ((i,x)::(j,-x)::w) ((hw.cons j _ h.neg).cons i _ h) hk)
lemma period0 (hs:Cour μ)(hk:flex K)(h:TouchF F){t:ℝ}: Pass (K t) (F t) μ := by
    intro l; have he : ContDiff ℝ ∞ (fun p:P=> trc (K t) p (F t) l):= by
        let w:tagSmooth P A P:= l.map fun i=> (i.1,fun _=>i.2); have hb : ∀ p,walk0 w p=l:= by simp [walk0,w, Function.comp_def]
        convert! flex_pays h hk (fun _=>t) contDiff_const (fun p:P=>p) contDiff_id (w:=w) ?_ using 1; · simp_rw [hb];
        intro i hi; obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hi; exact contDiff_const
    exact cafe μ hs he.continuous
lemma loop_on (hs:Cour μ)(hk:flex K)(h:TouchF F): TouchF (fun t=> orbit (K t) μ (F t)):= by
    intro E _ _ f w hw hf; simp_rw [finite_cc μ (period0 μ hs hk h),Ccy]
    let U:P×E→ℝ:= (f∘ Prod.snd); let M:tagSmooth (P× E) A P:= easy Prod.snd w
    have HV : Trail M:= hw.comp contDiff_snd; have hx:= flex_pays h hk U (hf.comp contDiff_snd) Prod.fst contDiff_fst HV; simpa only [U,M,Trail.comp_walk,Function.comp_apply] using (Lot μ hs hx).contDiff

omit [Fintype A] [MeasurableSpace P] [BorelSpace P] [FiniteDimensional ℝ P] in
lemma deskLift (h:TouchF F): TouchF (fun u l=> ∫ s in 0..u,F s l):=fun E _ _ f w hw hx=> by
    let T (x:ℝ× E):= F x.1 (walk0 w x.2); have ht : ContDiff ℝ ∞ T:= by convert h (ℝ×E) Prod.fst _ (Trail.comp hw contDiff_snd) contDiff_fst using 1; ext; simp [T, Trail.comp_walk]
    exact (park ht).comp (hx.prodMk contDiff_id)
end YM.MS.Heat
