import YM.FormalBulk08.Sierra.Ahead
/-! Multi-mark port on infinite cover. At finite lag pipeline computes
whole products, ordinary, after the common conditional denominator in
canonical/Ward recursors. Never treats mark labels as independently
sampled link variables. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
def diplex (p:Lava.Veil V)(q:Lava.Veil V)(r:ℕ):Tile V r:= ∑ i∈(Finset.HasAntidiagonal.antidiagonal r).attach,lengthen (Finset.HasAntidiagonal.mem_antidiagonal.mp i.property) (sand (clutch (p i.val.1) (q i.val.2)))
def duplexB (p q: OrbitV V): OrbitV V:= fun e r=> ∑ i∈Finset.HasAntidiagonal.antidiagonal e, diplex (p i.1) (q i.2) r
lemma spelled (p q: OrbitV V)(e r:ℕ): Agate (duplexB p q e r):= Agate.sums _ fun _ _=> Agate.sums _ fun _ _=> length_agate _ (agate_sand (clutch _ _))
lemma dup_grades {p q:OrbitV V}(h:Young p l)(g:Young q t): Young (duplexB p q) (l+t):= by
   intro e r he; by_contra hp; unfold Yield at hp; apply he
   apply Finset.sum_eq_zero; intro x hx; apply Finset.sum_eq_zero; intro y _; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx; have hM:=Finset.HasAntidiagonal.mem_antidiagonal.mp y.property
   by_cases hv:y.val.1≤ l+x.1
   · have hq:q x.2 y.val.2=0:= by by_contra hh;have hh:=g _ _ hh;unfold Yield at hh; omega
     rw [hq,show ∀ V : Tile V y.val.1, clutch V (0:Tile _ y.val.2)=0 from fun V=>by ext v;simp [clutch],sand_nil,length_void]
   have hp:p x.1 y.val.1=0:=by by_contra hh;exact hv (h _ _ hh)
   rw [hp,show clutch (0:Tile _ y.val.1) (q x.2 y.val.2)=0 by ext v;simp [clutch],sand_nil,length_void]
lemma clasp_cash {K:Reach V}{o: V}{p:Tile V m}{q:Tile V r}(h:Knoxville K σ o p B)(e:Knoxville K σ o q C)(hs:0≤σ): Knoxville K σ o (clutch p q) (B*C):= by simpa [K.self] using knox_clasp h e hs o
lemma dip_cash {p q:OrbitV V}{x:V}{R:Reach V}(h:∀ a≤E,∀ r, ∃ A,Knoxville R σ x (p a r) A)(he:∀ b≤E,∀ r,∃ B,Knoxville R σ x (q b r) B)(hs:0≤σ) : ∃ B:ℝ, Knoxville R σ x (duplexB p q E r) B:= by
   have ht(i:ℕ×ℕ)(hi:i∈Finset.HasAntidiagonal.antidiagonal E):∃ B:ℝ, Knoxville R σ x (diplex (p i.1) (q i.2) r) B:= by
       rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi
       choose B b using fun (j:ℕ)=> h i.1 (by omega) j
       choose C c using fun j:ℕ=>he i.2 (by omega) j
       exact ⟨_,knox_sum _ (K:=fun z=>(B z.val.1*C z.val.2)) (fun v _=>(clasp_cash (b v.val.1) (c v.val.2) hs).polish.rename _)⟩
   choose! B b using ht; exact ⟨_, knox_sum _ b⟩
variable [Fintype V]
lemma marble_product (p q: TypeR V) (r): marble r (p*q)=diplex (fun m=>marble m p) (fun m=>marble m q) r:= by
    apply facade_unique (marble_agate _ _) (Agate.sums _ (fun _ _=> length_agate _ (agate_sand (clutch _ _))))
    rw [marble_grade,comp_glue,map_sum]; simp_rw [facade_length,sand_facade, facade_clutch,marble_grade]
    exact (Finset.sum_attach _ _).symm
lemma product_read (p q:Pap V):rancho (p*q)=duplexB (rancho p) (rancho q):= by
    funext e r; rw [rancho,coeff_mul];simp_rw [←canyon_eq,map_sum,canyon_eq,marble_product];rfl

def doubled (p q:Waves V): Waves V:= fun n e r=> ∑ i∈Finset.HasAntidiagonal.antidiagonal n, duplexB (p i.1) (q i.2) e r
lemma posted (p q:Heat ℝ V): posting (p*q)=doubled (posting p) (posting q):= by
    funext n e r; rw [Lava.posting,readSlice,coeff_mul, Polynomial.finsetSum_coeff] -- name
    simp_rw [Polynomial.coeff_mul,←canyon_eq,map_sum,canyon_eq,marble_product]; unfold doubled duplexB; rw [Finset.sum_comm]; rfl
end YM.FormalBulk08.Vale
