import YM.XSpace.Fleeces
/-!
# Vertex window price and alarms
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Chart2 Graph3 Chiral Gland Relief Season Octave Lattice MvPolynomial Asymptotics Player
open scoped Topology BigOperators Classical
variable {G:Gauge} {W:Initialize G}{ι:Type} {a:ι→ℝ}{L:Filter ι}{c:Shade.Cut} {x y z:ι→Cover}{u v b:E4}
local notation "W₁" => G.ColorIndex
variable (P Q R: Player W)(g:G.Simple)
abbrev country (x y z:Cover)(A:Stamp G) := Uplands x y z (P.origin g) (Q.origin g) (R.origin g) A
lemma total (σ:Bool)(i:Name G): aimed G σ i∈Trio G 0 0 0:= by rw [trio3]; exact Submodule.mul_mem_mul (k₁ (stand_h σ i)) (stance₂ σ i)
lemma courtesy {I:Type*}(x y z:Cover)(A:I→Stamp G)(p:Finset I)(h:∀ i∈p,A i∈ Trio G 0 0 0): country P Q R g x y z (∑ i∈p,A i)=∑ i∈p,country P Q R g x y z (A i):=by
  induction p using Finset.induction_on with | empty=> simp [country,Uplands,feet] | insert i p hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; unfold country; have he := fun q H => h q (Finset.mem_insert_of_mem H); rw [uplands_add (P.visit g) (Q.visit g) (R.visit g) x y z _ _ (h i (Finset.mem_insert_self ..)) (Submodule.sum_mem _ he)]; exact congr_arg (_+·) (ih he)
private lemma contra (x y z:Cover){A B: Stamp G}(h:A∈ Trio G 0 0 0)(h':B∈Trio G 0 0 0): country P Q R g x y z (A-B)=country P Q R g x y z A-country P Q R g x y z B:=by apply eq_sub_of_add_eq; rw [← show country P Q R g x y z _=_+_ from uplands_add (P.visit g) (Q.visit g) (R.visit g) x y z (A-B) B (Submodule.sub_mem _ h h') h']; rw [sub_add_cancel]
def latch (x y z:Cover) : ℂ := country P Q R g x y z (∑ i:PlaqAxes,V3 G (tile i))
def located (c:Shade.Cut)(u v b:E4):ℂ:=∑ k:Name G,air P Q R false k c u v b
variable (T:Captain c L a x y z u v b)
include T in
lemma tone [NeBot L][L.IsCountablyGenerated](hq:Q.σ=false)(hr:R.σ=false) : Named L a 6 (fun i=> latch P Q R g (x i) (y i) (z i))
     (located P Q R c u v b + kernel P R false v u b Q.elem + kernel P Q false b u v R.elem):=by
  let f (k:Name G)(x y z:Cover):= country P Q R g x y z (aimed G false k); let a₀(k:Name G) := air P Q R false k c u v b; let a₁(k:Name G):= if k=Q.elem then kernel P R false v u b k else 0; let a₂(k:Name G):= if k=R.elem then kernel P Q false b u v k else 0
  let F (i:ι):=country P Q R g (x i) (y i) (z i) (farMinus G); apply Named.wallet (g:=F); swap
  · unfold latch F; simp_rw [← contra P Q R g _ _ _ (Submodule.sum_mem _ (fun i _=> k₃ (primary (G:=G) i))) (Submodule.sum_mem _ (fun i _=> total false i))]; exact Named.low (pays_out (P.visit g) (Q.visit g) (R.visit g) T.led T.grant (flung G)) T.led
  have he(k:Name G): Named L a 6 (fun i=> f k (x i) (y i) (z i)) (a₀ k+a₁ k+a₂ k):=by
    let h:= ((aired P Q R g false k T).add (aired₀ Q P R g false k T.hop hq)).add (aired₀ R P Q g false k T.turn.turn hr); apply Named.congr h; intro i; exact (strapT P Q R g false k (x i) (y i) (z i)).symm
  have hp:= Named.sum _ _ _ (fun k (_:k∈Finset.univ)=> he k); simp_rw [Finset.sum_add_distrib] at hp; rw [show (∑ k,a₁ k)=kernel P R false v u b Q.elem from by simp [a₁],show (∑ k,a₂ k)=kernel P Q false b u v R.elem from by simp [a₂]] at hp; exact hp.congr fun i=> (courtesy P Q R g (x i) (y i) (z i) _ _ (fun i (_:i∈Finset.univ)=>total false i)).symm -- maybe dot congr tendsto
omit P Q R in -- L binder?
lemma real_seal (W:Initialize G)(p q r:Name G): located (mum W p) (mrs W q) (mrs W r) c u v b= ↑(br p.2 q.2 r.2*(∑ t:Chiral.P,sweepT c p.1 t q.1 r.1 u v b)):=by
  unfold located; rw [Fintype.sum_prod_type, Finset.mul_sum, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _; unfold air heel; rw [Finset.sum_eq_single p.2]; dsimp only; rw [show Player.color (mum W p)=p.2 from rfl,χ_self,one_mul]
  · intro j _ hj; dsimp only; rw [show χ (mum W p).color j=0 from if_neg (show j≠(mum W p).color from hj),zero_mul,zero_mul]; simp
  simp
end YM.XSpace.Finale
