import YM.XSpace.Sample

/-!
# Finite localization of vertices

Spell out representation tools for the first-order diagrams before Wick expansion, not
bounding by polynomial degree without graph control. In particular obtain the shape of V3
using the BCH struct does not require choosing a Lie basis that is globally consistent among cities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Outline
open Function Lattice RG Wilson Source Source.Drops Labels Chart2 Bid Work
open MvPolynomial Next.Rank.Normal Finsupp
open scoped BigOperators Topology InnerProductSpace
variable {G:Gauge}{R Q:Type*}[AddCommGroup R][One R][AddCommGroup Q][One Q] {n d:ℕ} {H: Hol G}
abbrev Bone (G:Gauge) (R:Type*):= Rollers (Edges2 R) G
abbrev Wing (G:Gauge)(R:Type*):= Face R× G.ColorIndex

def ringBell (p:Wing G R): Bone G R →₀ℂ :=
  let a:=p.1; let i:=a.2.val.1; let j:=a.2.val.2; let k:=p.2; let x:=a.1
  single ((x,i),k) 1+ single ((x+step i,j),k) 1- single ((x+step j,i),k) 1-single ((x,j),k) 1
lemma ring_at (a:Wing G R) (u:LogLinks R G): pit u (glyph (ringBell a))= (linearFace a.1 u a.2:ℂ):=by unfold ringBell; simp [map_add,map_sub,glyph, pit, angular, numbers]
lemma ring_shift (c:Chart R Q)(p:Face R)(a:G.ColorIndex): c.pull (glyph (ringBell (p,a)))=glyph (ringBell ((c.site p.1,p.2),a)):=same (fun A=> by rw [Chart.pull_point,ring_at,ring_at,c.pflux])

-- Entitle even the interacting column correction as bounded degree (no radius estimate
-- needed here) because single-j support is already finite. For the zero-degree piece
-- need exact color-horizontal representation.
def beanCode (S:Survey G H d)(x:Four R)(k: Key G): Wing G R→₀ℂ:= ∑ i:Top.Bean S, (↑(Top.bills S (Survey.component k) i):ℂ) • single (slotPoint x (S.looks i.1),i.2) 1
lemma ear_key (S:Survey G H d)(x:Four R)(k:Key G): leftKey S x k=glyph (Finsupp.linearCombination ℂ ringBell (beanCode S x k)):=by
  apply same; intro A
  rw [pit_left,beanCode]; simp only [_root_.map_smul,_root_.map_sum,Finsupp.linearCombination_single,one_smul,ring_at]
  conv_lhs=> rw [primary_at,← Top.bean_reconstruct S (spectra S x A),map_sum,map_sum]
  refine Finset.sum_congr rfl fun i _=> ?_
  rw [map_smul,map_smul,Complex.real_smul,smul_eq_mul]; rw [mul_comm]; rfl

def script (S: Survey G H d)(x:Four R) := exchange (beanCode S x)
def score (G:Gauge)(R:Type*) [AddCommGroup R][One R] := exchange (ringBell (R:=R) (G:=G))
lemma bolt (S:Survey G H d)(x:Four R)(p:Labels.Pol G): score G R (script S x p)=p0 S x p := by
  unfold script score p0 toy; induction p using MvPolynomial.induction_on with
  | C a=> simp [PowerSeries.algebraMap_apply,MvPolynomial.algebraMap_eq]
  | add p q hp hq=> simp only [map_add,hp,hq]
  | mul_X p i hp=> rw [map_mul,map_mul,map_mul,map_mul,hp]; rw [exchange_x,aeval_X, constant_knit, ear_key]; congr 1; -- maybe known exchange-glyph
                   generalize beanCode S x i=v; induction v using Finsupp.induction_linear with
                   | zero=> simp
                   | add i j hi hj=> simp only [map_add, hi,hj]
                   | single i a=> simp

-- Factor the cubic using finitely many native bonds
abbrev Couplet (R:Type*):= Edges2 R × Edges2 R
def witness (U:LogLinks R G)(w:Couplet R →₀ℝ): G.Color := Finsupp.linearCombination ℝ (fun i:Couplet R=>G.ad (U i.1) (U i.2)) w
lemma total_path (G: Gauge) (x:Four R)(p:Walk): ∃ m:Edges2 R→₀ℝ,∀ U:LogLinks R G,tallyPath x p U= Finsupp.linearCombination ℝ U m:=by
  induction p generalizing x with
  | nil=>exact ⟨0, fun U=> (map_zero _).symm⟩
  | cons d w ih=> obtain ⟨m,hm⟩:= ih (x+d.vec); rcases d with ⟨i,h|h⟩
                  · refine ⟨single (x,i) 1+m,fun A=>?_⟩; rw [tallyPath,LinearMap.add_apply,hm,map_add,Finsupp.linearCombination_single,one_smul]; exact congr_arg (·+_) (touch_pos x i A)
                  refine ⟨single (x-step i,i) (-1)+m,fun A=>?_⟩; rw [tallyPath,LinearMap.add_apply,hm,map_add,Finsupp.linearCombination_single,neg_one_smul]; exact congr_arg (·+_) (touch_neg x i A)
lemma priced (G:Gauge) (x:Four R)(p:Walk): ∃ m:Couplet R→₀ℝ,∀ U:LogLinks R G,(travel (native U) x p).c=witness U m:=by
  have he (i:Edges2 R)(b:Edges2 R→₀ℝ): ∃ w:Couplet R→₀ℝ,∀ U:LogLinks R G, G.ad (U i) (Finsupp.linearCombination ℝ U b)=witness U w:=by
    induction b using Finsupp.induction_linear with
    | zero=> exact ⟨0, by simp [witness]⟩
    | add a b h1 h2=> obtain ⟨w,hw⟩:=h1; obtain ⟨v,hv⟩:=h2; exact ⟨w+v,fun U=> by simp only [map_add,hw,hv,witness]⟩
    | single j b=> exact ⟨single (i,j) b,fun U=> by simp [witness]⟩
  induction p generalizing x with
  | nil=>exact ⟨0,fun U=> (map_zero _).symm⟩
  | cons d p ih=>
    obtain ⟨a,ha⟩:=total_path G (x+d.vec) p; obtain ⟨b,hb⟩:=ih (x+d.vec)
    rcases d with ⟨i,h|h⟩
    · obtain ⟨v,hv⟩:= he (x,i) a; refine ⟨b+(1/2:ℝ) • v,fun U=>?_⟩
      rw [travel,Drift.c_mul, trip_a, touch_a, touch_c, ha,hb]; change ((touch x (posDir i)) 0)+ _+(1/2:ℝ) • G.ad (touch x (posDir i) U) _= _; rw [map_zero,touch_pos, hv]; simp [witness]
    obtain ⟨v,hv⟩:= he (x-step i,i) a; refine ⟨b-(1/2:ℝ) • v, fun U=>?_⟩
    rw [travel,Drift.c_mul,trip_a,touch_a,touch_c,ha,hb]; change ((touch x (negDir i)) 0)+_+(1/2:ℝ) • G.ad (touch x (negDir i) U) _=_; rw [map_zero,touch_neg, _root_.map_neg,LinearMap.neg_apply,hv]; simp [witness,sub_eq_add_neg]

def castanet (p:Face R)(G:Gauge):= (priced G p.1 (square p.2.val.1 p.2.val.2)).choose
lemma plays (p:Face R)(A:LogLinks R G): acc p A = witness A (castanet p G):=(priced ..).choose_spec A

def vcost (i j k:G.ColorIndex):ℝ:=inner ℝ (basisC G i) (G.ad (basisC G j) (basisC G k))
lemma v_cost (a b d:G.Color): inner ℝ a (G.ad b d)=∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex,vcost i j k*(a i*b j*d k):=by
  have h (x:G.Color): x=∑ i:G.ColorIndex,x i • basisC G i:= Eq.symm ((basisC G).sum_repr x)
  conv_lhs=> rw [h a, sum_inner]; arg 2; ext i; rw [h b, _root_.map_sum G.ad,LinearMap.sum_apply,inner_sum]; arg 2; ext j; rw [h d,map_sum,inner_sum]
  simp only [_root_.map_smul, LinearMap.smul_apply]; simp_rw [real_inner_smul_left,real_inner_smul_right]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_; unfold vcost; ring
lemma v_off (i j k:G.ColorIndex)(h:i=j∨j=k∨i=k): vcost i j k=0:=by
  rcases h with h|h|h <;> unfold vcost <;> rw [h]
  · rw [Drift.ad_swap,inner_neg_right,Drift.ad_e,neg_zero]
  · rw [Drift.ad_same,inner_zero_right]
  apply Drift.ad_e

lemma v_as_sum (p:Face R): V3 G p=∑ w∈(castanet p G).support,∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex,
    C (↑(castanet p G w*vcost i j k):ℂ)*(glyph (ringBell (p,i))*X (w.1,j)* X (w.2,k)):=by
  apply same; intro A; rw [price_at,diagnostic,plays]; conv_lhs=> unfold witness; simp only [linearCombination_apply,Finsupp.sum,inner_sum,real_inner_smul_right]
  simp only [v_cost,Finset.mul_sum,_root_.map_sum,Complex.ofReal_sum,map_mul,ring_at]; simp only [pit,MvPolynomial.aeval_C,MvPolynomial.aeval_X,Algebra.algebraMap_self,RingHom.id_apply]; push_cast
  apply Finset.sum_congr rfl; intro w _; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; unfold numbers; ring
end YM.XSpace.Outline
