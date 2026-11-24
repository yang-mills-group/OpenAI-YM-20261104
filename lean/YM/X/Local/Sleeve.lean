import YM.X.Local.Quay
/-!
# longitudinal polynomial variations. ∆ stencil & Tilt order. width exponent of scalar gauge parameter. No commitment to sym σ.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crystal
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow Shelf Ocean Fielding CellsInt
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
section
variable [NormedAddCommGroup V][NormedSpace ℝ V]
def lease (n:ℕ)(f:Cover→V): Prop:= ∀ t:Fin n→Axis,jumped t f=0
namespace lease
variable {f g:Cover→V}
lemma zero : lease n (0:Cover→V):= fun t=> map_zero _
lemma zero_for (h:lease 0 f): f=0:= h (fun i=> Fin.elim0 i)
lemma extend (h:lease n f)(ht:n≤k): lease k f:= by
   induction ht with
   | refl=>exact h
   | step hp ih=> intro l; rw [jumpIt,jumps,hopped,← jumpIt,ih]; funext; unfold stepValue; rw [Pi.zero_apply,Pi.zero_apply,sub_self]
lemma take_step (h:lease (n+1) f)(i:Axis): lease n (stepValue f i):= fun v=> h (Fin.cons i v)
lemma fetch (h:∀ i:Axis,lease n (stepValue f i)):lease (n+1) f:= fun v=> h (v 0) (Fin.tail v)
lemma translate (h:lease n f)(z:Cover):lease n (fun y=>f (y+z)):= fun l=> funext (fun y=> (jump_shift l f y z).trans (congr_fun (h l) (y+z)))
lemma add (h:lease n f)(hp:lease n g): lease n (f+g):= fun t=>by rw [map_add,h t,hp t,zero_add]
lemma smult (h:lease n f)(a:ℝ): lease n (a • f):= fun v=> by rw [map_smul,h v,smul_zero]
-- neat product n+m levels via induction on explicit proof k≥ m+n lower.
lemma union (B:V→ₗ[ℝ] V→ₗ[ℝ] V)(hf:lease (k+1) f)(hg:lease (m+1) g):lease (k+m+1) (fun x=> B (f x) (g x)):= by
   suffices h:∃ n:ℕ,n=k+m+1∧lease n (fun x=> B (f x) (g x)) by obtain ⟨n,rfl',h⟩:=h; exact rfl' ▸ h
   have he(i:Axis)(f g:Cover→V):stepValue (fun x=> B (f x) (g x)) i=(fun x=>B (f (x+step i)) (stepValue g i x))+(fun x=>B (stepValue f i x) (g x)):= by ext1 x; simp only [stepValue,map_sub,Pi.add_apply,LinearMap.sub_apply];abel
   have hu(n:ℕ):∀ k m:ℕ,k+m=n→∀ f g:Cover→V,lease (k+1) f→ lease (m+1) g → lease (n+1) (fun x=> B (f x) (g x)):= by
      intro k m hb; induction n using Nat.strong_induction_on generalizing k m with
      | h n IH=>
         intro f g hf hg; apply fetch; intro i; rw [he i f g]; apply add
         · cases m with
           | zero=> rw [zero_for (hg.take_step i)]; simp only [Pi.zero_apply,map_zero]; exact zero
           | succ m=> have hx: k+m<n:= (by omega); rw [show n=k+m+1 by omega]; exact IH (k+m) hx k m rfl _ _ (hf.translate (step i)) (hg.take_step _)
         cases k with
         | zero=> rw [zero_for (hf.take_step i)]; simp only [Pi.zero_apply,map_zero, LinearMap.zero_apply]; exact zero
         | succ k=> have ht:k+m<n:= (by omega); rw [show n=k+m+1 by omega]; exact IH (k+m) ht k m rfl _ _ (hf.take_step _) hg
   exact ⟨k+m+1,rfl,hu (k+m) k m rfl f g hf hg⟩
end lease
end

local notation "K" => Curly G
local notation "H" => Hair G
variable (s:Okay G k) (x:Brush G)
lemma own_lease : lease (k+1+1) (phase s):= fun l=> higher (windP_sym (s - rightCur k s).val) _ (by omega) l
def mess : Fan G→ₗ[ℝ] Fan G := Finsupp.linearCombination ℝ (θRow (phase s))
lemma mess_tick (f:Fan G) :flatL x (mess s f)= flatL (θ (phase s) x) f:=by
   unfold mess; rw [LinearMap.map_finsupp_linearCombination]; apply congr_arg (fun g:H→ℝ=> Finsupp.linearCombination ℝ g f); funext i; exact (struck ..).symm
lemma read_mess (f:Fan G): tilt (str (phase s)) (glyph (com f))=glyph (com (mess s f)):= by
    apply snap_ext; intro x; rw [strokes,stroke,link_g,com_read]; rw [carbon, snap, aeval_C]; exact congr_arg Complex.ofReal (mess_tick s x f).symm
lemma fun_launch (A:Brush G)(l:Axis)(z:Cover):
    raising l (θ (phase s) A) z=G.ad (raising l A z) (eta (phase s) (z,l)):=rfl
lemma reach_eta (j:Axis): lease (k+1+1) (fun z:Cover=> eta (phase s) (z,j)):= lease.smult (lease.add ((own_lease s).translate (step j)) (own_lease s)) _
lemma piston (A:Brush G)(h:Cloudless (m+1) A) : Cloudless (m+k+1+1) (θ (phase s) A):= by
    intro v j; rw [show raising j (θ (phase s) A)=_ from funext (fun z=> fun_launch s A j z)]; have he : lease (m+1) (raising j A):= fun l=>h l j; have h': lease (m+k+1+1) (fun z=> G.ad (raising j A z) (eta (phase s) (z,j))):= by rw [show m+k+1=m+(k+1) by omega]; exact lease.union G.ad he (reach_eta s j)
    exact h' v
lemma grad_tilt (f:Fan G)(hf:f∈Reed.grads G d): mess s f∈ Reed.grads G (d-(k+1)):= by
    generalize hh:d-(k+1)=m; cases m with
    | zero=> rw [grade0]; simp
    | succ m=> refine (cloud_ann _).mpr (fun A h=>?_); rw [mess_tick]; exact (cloud_ann f).mp hf _ (cloud_rise (piston s A h) (by omega))
end YM.PositionX.Crystal
