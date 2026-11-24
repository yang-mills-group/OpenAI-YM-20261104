import YM.FormalBulk08.Annex.Fits

/-! keep horizon atlas, transform each chosen path expression to the
centered address support using Π operators. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Annex
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{n:Side}{r t j k u l e E D:ℕ}{A B C σ η:ℝ}{o:Loc G 1}
open Spigot Pose
variable {L:Studio D→ₗ[ℝ] Studio D}{M:Spigot.Cabin D I G r}{Q:Herald} {T S:Anthem D G}

lemma chart_billing (H:Pass D C L)(g:Woodsy o σ A E T): Woodsy o σ (C*A) E (T ∘ L):= by
    have h :0≤C:=zero_le_one.trans H.safe; refine ⟨mul_nonneg h g.height,fun i p r x=>?_ ⟩; refine (g.precincts i p r (L x)).mono ?_; rw [mul_comm C, mul_assoc]; exact mul_le_mul_of_nonneg_left ((H.price x).trans (mul_le_mul_of_nonneg_left (comp_le x) h)) g.height
lemma chart_entry (_H:Pass D C L){B:Cabin D I G r}(h:B.atoms=M.atoms)(p:B.pulse=(fun i=> (M.pulse i).comp L))(e:ℕ): struck B e=struck M e ∘ L := by
   funext v j r; unfold struck; dsimp only [Function.comp_apply]; split
   · unfold candle; rw [h,p];rfl
   rfl
def Brooted (p:Spigot.Path D G):= ∀ i,Concentrated (p.cabin.plus i)∧ Concentrated (p.cabin.minus i)
def grows (C:ℝ)(u D:ℕ):=C+9^u*Real.exp 8*(Fintype.card (Brush D)*C)
lemma grown_ge (h:0≤C): C≤grows C u D:= le_add_of_nonneg_right (by positivity)
lemma merit_charts (H:Pass D C L)(hs:0≤σ)(hp:σ≤1) (p:Spigot.Path D G)(e:Merit Q o p l u E σ A):∃ q:Spigot.Path D G, Merit Q o q l u E σ (grows C u D*A) ∧ q.grade=p.grade ∧ q.rank=p.rank ∧ Brooted q∧ struck q.cabin q.grade= struck p.cabin p.grade ∘ L:=by
   obtain ⟨Y,P,W,v,h⟩:=portfolio H e.income hs hp; let q: Spigot.Path D G:= ⟨p.rank,p.grade,p.I,Y⟩; have hx:= e.costs.height; have he:= chart_entry H W P p.grade; refine ⟨q,⟨e.alive,e.meets,h.shrink le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (zero_le_one.trans H.safe)) hx),fun i x=>?_,?_⟩,rfl,rfl,v,he⟩
   · change ∃ z,(Y.atoms i).leg x=_;rw [W]; exact e.set ..
   change Woodsy _ _ _ _ (struck Y p.grade); rw [he];exact wood_mono (chart_billing H e.costs) le_rfl (mul_le_mul_of_nonneg_right (grown_ge (zero_le_one.trans H.safe)) hx)
lemma authoring (H:Pass D C L)(hs:0≤σ)(hp:σ≤1)(P:List (Spigot.Path D G))(p:∀ x∈ P,Merit Q o x l u E σ A)(e:∀ x∈ P,j≤x.grade ∧ x.grade < j+k):∃ S:List (Spigot.Path D G), S.length=P.length ∧ (∀ x∈ S, Merit Q o x l u E σ (grows C u D*A)∧Brooted x)∧ (∀ x∈ S,j≤ x.grade∧ x.grade < j+k)∧ binding S=binding P ∘ L := by
   induction P with
   | nil=> exact ⟨[],rfl,by simp,by simp,by simp⟩
   | cons x U ih=>
      obtain ⟨S,s,b,hZ,T⟩:=ih (fun _ he=> p _ (List.mem_cons_of_mem _ he)) (fun _ he=>e _ (List.mem_cons_of_mem _ he)); obtain ⟨y,hy,Y,h,Q',he⟩:= merit_charts H hs hp x (p _ (List.mem_cons_self ..)); refine ⟨y::S,by simp [s],fun p h=> ?_,fun p h=> ?_,?_⟩
      · obtain rfl|h:=List.mem_cons.mp h; exact ⟨hy,Q'⟩; exact b _ h
      · obtain rfl|h:=List.mem_cons.mp h; rw [Y]; exact e _ (List.mem_cons_self ..); exact hZ _ h
      rw [binding_cons,he,T,binding_cons];rfl
lemma author (D u:ℕ) :∃ B:ℝ,1≤ B∧ ∀ (o:Loc G 1)(Q:Herald)(T:Anthem D G)(i k l E:ℕ) σ A,0≤σ→σ≤1→ (∀ x y,compress D x=compress D y→T x=T y)→ ∀ P,Litany Q o P l u E i k σ A T→ ∃ M, Litany Q o M l u E i k σ (B*A) T∧ ∀ x∈ M,Brooted x:= by
   obtain ⟨C,L,H⟩:= extension D; have he := grown_ge (u:=u) (D:=D) (zero_le_one.trans H.safe); refine ⟨grows C u D,H.safe.trans he,fun o Q T i k l E σ A hs hp g P v=>?_⟩; obtain ⟨S,s,b,h,U⟩:= authoring H hs hp P v.origin v.fortune
   refine ⟨S,⟨⟨fun x p=>(b x p).1,?_⟩,s.trans_le v.build,h,fun j hj x=>?_⟩,fun x hx=>(b x hx).2⟩
   · rw [U]; exact wood_mono (chart_billing H v.bill) le_rfl (mul_le_mul_of_nonneg_right he v.bill.height)
   rw [U,← g _ _ (H.opake x)]; exact v.agrees j hj _ -- danger rw g variable
end YM.FormalBulk08.Annex
