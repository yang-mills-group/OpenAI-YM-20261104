import YM.X.Braid.Warp
import YM.X.Site.Field
/-! # Shift hair atlas at periodic covariance -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Fielding
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric
open Reed Stems Hinge Braid
open scoped Topology BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k:ℕ} {G:Gauge}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "H"=> Hair G
variable (x y z:Cover)(f g:Fan G)(p:Hair G)(v:Brush G)
def pointB (x:Cover)(p:Hair G):H:=((x+p.1.1,p.1.2),p.2)
def leadsL (x:Cover): Module.End ℝ (Fan G):= Finsupp.lmapDomain ℝ ℝ (pointB x)
@[simp] lemma leads_single (c:ℝ): leadsL x (Finsupp.single p c)=Finsupp.single (pointB x p) c:=Finsupp.mapDomain_single
lemma leads_comp: leadsL x (leadsL y f)=leadsL (x+y) f:= by
    induction f using Finsupp.induction_linear with
    | zero=>simp
    | add a b h g=>simp [h,g]
    | single i k=> rw [leads_single,leads_single,leads_single]; unfold pointB; rw [add_assoc]
@[simp] lemma leads_zero : leadsL 0 f=f:= by
    induction f using Finsupp.induction_linear with
    | zero=>simp
    | add a b h g=>simp [h,g]
    | single i k=> simp [pointB]
def lowerP (x:Cover): Module.End ℝ (Brush G):= LinearMap.pi fun i:Pin=> LinearMap.proj (x+i.1,i.2)
lemma lowerP_pin : (lowerP x v) p.1=v (pointB x p).1:= rfl
@[simp] lemma lowerP_zero (A:Brush G):lowerP 0 A=A:= by ext1 p; change A (0+p.1,p.2)=_; rw [zero_add]
lemma tasteL : flatL (lowerP x v) f=flatL v (leadsL x f):=by
   induction f using Finsupp.induction_linear with
   | zero=>simp
   | add a b h p=>simp [h,p]
   | single i k=> rw [leads_single,flatL,flatL,Finsupp.linearCombination_single,Finsupp.linearCombination_single]; rfl
lemma jets_lead (l:Fin k→Axis): leadsL x (jetRow k l p)=jetRow k l (pointB x p):= by
   induction k generalizing p with
   | zero=> simp [jetRow]
   | succ k IH=> rw [jetRow,map_sub,IH,IH,jetRow]; unfold pointB; rw [add_assoc] -- direction
lemma grad_lead (h:f∈ Reed.grads G k): leadsL x f∈Reed.grads G k:=by
   induction h using Submodule.span_induction with
   | mem i hi=> obtain ⟨⟨p,b⟩,rfl⟩:=hi; unfold Function.uncurry; rw [jets_lead]; apply grad_row
   | zero=>rw [map_zero]; exact Submodule.zero_mem _
   | add a b h g y t=> rw [map_add]; exact Submodule.add_mem _ y t
   | smul a i h g=> rw [map_smul];exact Submodule.smul_mem _ _ g
lemma leads_arc (z:Address G) : leadsL x (signal_arc z)=signal_arc (x+z.1,z.2):=by simp only [signal_arc,Stems.arc,map_add,map_sub,leads_single]; unfold pointB; simp only [add_assoc]
lemma horizontal_lead (h:f∈Reed.Horizontal G): leadsL x f∈Reed.Horizontal G:=by
   induction h using Submodule.span_induction with
   | mem i hi=> obtain ⟨p,rfl⟩:=hi; rw [leads_arc]; exact Submodule.subset_span ⟨_,rfl⟩
   | zero=>rw [map_zero]; exact Submodule.zero_mem _
   | add a b h g y t=> rw [map_add]; exact Submodule.add_mem _ y t
   | smul a i h g=> rw [map_smul];exact Submodule.smul_mem _ _ g
lemma fan_triangle (h:f∈ Reed.grads G k)(i:Axis): leadsL (step i) f - f ∈ Reed.grads G (k+1):= by
   induction h using Submodule.span_induction with
   | mem z h=> obtain ⟨⟨l,b⟩,rfl⟩:= h; unfold Function.uncurry; rw [jets_lead]; have he : pointB (step i) b= ((b.1.1+step i,b.1.2),b.2) := by unfold pointB;rw [add_comm]
               rw [he]; exact grad_row (Fin.cons i l) b -- parser?
   | zero=>rw [map_zero,sub_zero]; exact Submodule.zero_mem _
   | add a b h g y t=> rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ y t
   | smul a i h g=> rw [map_smul,← smul_sub];exact Submodule.smul_mem _ _ g
lemma tau_lead (t:H): tau n (pointB x p) (pointB x t)=tau n p t:= by unfold tau pointB Braid.cane; rw [map_add,map_add,add_sub_add_left_eq_sub] -- lemma

def spend (n:Side)(x y:Cover): Fan G →ₗ[ℝ] Fan G→ₗ[ℝ] ℝ:= ((taste ∘ₗ leadsL y).flip ∘ₗ paints n ∘ₗ leadsL x)
lemma spent (n:Side): spend n x y f g = flatL (paints n (leadsL x f)) (leadsL y g):= taste_eval ..
lemma spent₀: spend n 0 0 f g=flatL (paints n f) g:=by rw [spent,leads_zero,leads_zero]
lemma symmetry : spend n x y f g= spend n y x g f:= (spent x y f g n).trans (Braid.commute ..) |>.trans (spent y x g f n).symm
lemma spend_single (l m:ℝ)(t:H): spend n x y (Finsupp.single p l) (Finsupp.single t m)=l*m*tau n (pointB x p) (pointB y t):= by
    rw [spent,leads_single,leads_single,flatL,Finsupp.linearCombination_single,text_paints,Finsupp.linearCombination_single,tau_swap]; change m*(l*_)=_;ring
lemma spend_lead : spend n (z+x) (z+y) f g=spend n x y f g:= by
    suffices h: spend (G:=G) n (z+x) (z+y)=spend n x y by rw [h]
    ext p t; simp only [LinearMap.coe_comp,comp_apply,Finsupp.lsingle_apply]; rw [spend_single,spend_single]; simp only [mul_one,one_mul]; rw [show ∀(x:Cover)(p:H),pointB (z+x) p=pointB z (pointB x p) from fun x p=>by unfold pointB; rw [add_assoc], show pointB (z+y) t=pointB z (pointB y t) by unfold pointB; rw [add_assoc],tau_lead]
lemma spend_subx : spend n x y (leadsL z f) g=spend n (x+z) y f g:= by rw [spent, leads_comp,spent]
lemma spend_suby : spend n x y f (leadsL z g)=spend n x (y+z) f g:= by rw [symmetry,spend_subx,symmetry]
end YM.PositionX.Fielding
