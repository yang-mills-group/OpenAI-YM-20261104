import YM.XSpace.Avenue

/-! # Price and Wick convention for the physical vertices -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Mu
open Lattice Trace Chart2 MvPolynomial Function Set Finsupp Next.Rank.Normal Contraction Outline Labels
open scoped Topology BigOperators
variable {G:Gauge}{d e:ℕ}

def freeCurl (p:Face ℤ)(i:G.ColorIndex):Fee G:=⟨1,Trace.touch p.1 p.2.val.1 p.2.val.2 [] i,touch_cane p.1 p.2.val.1 p.2.val.2 [] i⟩
def freeLeg (i:UnitIndex G): Fee G:= ⟨0,needle i,tariff _⟩
lemma ring_charge (p:Face ℤ)(i:G.ColorIndex): glyph (ringBell (p,i)) = harp (freeCurl p i).line:= Chart2.same fun A=>by rw [ring_at,leg_test, show (freeCurl p i).line=Trace.touch p.1 p.2.val.1 p.2.val.2 [] i from rfl,show probe _ A=_ from Trace.paid p.1 p.2.val.1 p.2.val.2 [] i A]; change _=(↑(Scale.crackle p.2.val.1 p.2.val.2 A p.1 i):ℂ); rw [Scale.plot _ _ p.2.property]
lemma wall_entry (w:Bone G ℤ): harp (freeLeg w).line=X w:= harps w

def throne (G:Gauge)(n d:ℕ):= Submodule.span ℂ (story '' {L:Word G | L.length=n∧debt L=d})
lemma throne_element (G:Gauge)(n d:ℕ): throne G n d≤elemental G d:=Submodule.span_mono (Set.image_mono fun _ h=>⟨h.2,fun _ _=> trivial⟩)
lemma stationed (p:Face ℤ): V3 G p ∈ throne G 3 4:=by
  rw [v_as_sum]; refine Submodule.sum_mem _ fun i _=> Submodule.sum_mem _ fun j _=> Submodule.sum_mem _ fun k _=> Submodule.sum_mem _ fun q _=> ?_
  rw [C_mul',ring_charge,← wall_entry (G:=G) (i.1,k), ← wall_entry (G:=G) (i.2,q)]; apply Submodule.smul_mem; refine Submodule.subset_span ⟨[freeCurl p j, freeLeg (i.1,k),freeLeg (i.2,q)], ⟨rfl,rfl⟩,?_⟩; simp only [read_word,mul_assoc,steam,mul_one]
private lemma same_q (i j:Bone G ℤ)(h:i.2≠j.2): (root G).cov i j=0:=by change coal _ i j=0; simp [coal,h]
private lemma two (i j:Bone G ℤ)(h:i.2≠j.2): milk (root G) (X i* X j)=X i* X j:=by
  have he : ∀ k:Bone G ℤ,milk (root G) (X k)=X k:= fun k=> by rw [← wall_entry k]; exact leg _
  rw [feeds, he, slit_X,same_q i j h,map_zero,add_zero]
private lemma three (i j k:Bone G ℤ)(h:i.2≠j.2)(p:i.2≠k.2)(q:j.2≠k.2): milk (root G) (X i* X j* X k)=X i* X j* X k:=by rw [mul_assoc,feeds,two j k q, slit_prod,same_q i j h,slit_X,same_q i k p];simp [map_zero]
@[simp] lemma opens_V (p:Face ℤ): flicker (V3 G p)= V3 G p:= by
  rw [v_as_sum]; simp only [map_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> Finset.sum_congr rfl fun q _=> ?_
  by_cases he: j=k∨k=q∨j=q; rw [v_off _ _ _ he]; simp
  push Not at he; obtain ⟨a,b,c⟩:=he; rw [C_mul',map_smul]; apply congr_arg; let K := (root G); have hs (z:Edges2 ℤ) : flicker (glyph (single (z,j) 1)* X (i.1,k) *X (i.2,q))= glyph (single (z,j) 1)* X (i.1,k) *X (i.2,q):=by simp only [glyph,Finsupp.linearCombination_single,one_smul]; exact three _ _ _ a c b
  unfold ringBell; simp only [_root_.map_add,_root_.map_sub,add_mul,sub_mul]; simp only [hs]
lemma encoded (x:Cover)(p:PlaqAxes):V3 G (x,p)=Trace.volume x (V3 G ((0:Cover),p)):=by rw [Trace.stained,Chart.v3]; simp [Chart.lug]

variable {H:Source.Hol G}(S: Survey G H d)
def headlines (i:Labels.Key G): Fee G:= ⟨i.1+1,ping S i,allows S i⟩
lemma headline (i:Labels.Key G): (headlines S i).cost= generation i:=by unfold generation Fee.cost headlines; simp only; omega
lemma reel_x (i:Labels.Key G): Encore.reel S 0 (X i)=harp (headlines S i).line:=by rw [Encore.reel,exchange_x,originate];rfl
lemma mood_monoid (i:Labels.Key G→₀ℕ) (c:ℂ): Encore.reel S 0 (monomial i c)∈ OnStage G (Finsupp.weight generation i):=by
  classical apply Extra.FD.per_factor i; rw [map_zero,show monomial (σ:=Labels.Key G) 0 c=C c from rfl,← mul_one (C c), C_mul',map_smul,map_one]; exact Submodule.smul_mem _ _ (one_go Stops)
  intro j k h; rw [monomial_add_single,pow_one,map_add,weight_single,one_smul,map_mul,reel_x,← headline S k]; exact productKeen Stops h (read_cut Stops _ (pings S k))
lemma briefing (p:Labels.Pol G)(h:IsWeightedHomogeneous generation p e): Encore.reel S 0 p∈ OnStage G e:=by rw [p.as_sum,map_sum]; refine Submodule.sum_mem _ fun i hi=> ?_; rw [← h (MvPolynomial.mem_support_iff.mp hi)]; exact mood_monoid S _ _
lemma move_reel (p:Labels.Pol G)(x:Cover): Encore.reel S x p=Trace.volume x (Encore.reel S 0 p):=by simp_rw [← Encore.tuned,Trace.stained,Chart.pull0]; simp [Chart.lug]
open Price (preparedL natural)
lemma status (v:On.Grade G d): Encore.reel S 0 (preparedL v).val∈ OnStage G d:= briefing S _ (natural v)
lemma vetting (v:On.Grade G d)(w: PlaqAxes) : Book G (d+4) (fun x:Cover=> tie G (Encore.reel S 0 (preparedL v).val) (V3 G (x,w))):=by
  conv => arg 3; ext x; rw [encoded x w]
  exact earned (good_read Stops _ (status S v)) (throne_element G 3 4 (stationed _))
end YM.XSpace.Mu
