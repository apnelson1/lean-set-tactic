import data.finset.basic
import data.fintype.basic 
import extensionality

namespace extensionality
instance finset_extensionality (T : Type) [fintype T] [decidable_eq T] :
  (boolean_algebra_extensionality (finset T) T) :=
{
  simpl_eq := by tidy,
  ext_top := by unfold_projs; finish,
  ext_bot := by tidy,
  ext_sdiff := by tidy,
  ext_le := by tidy, 
  ext_meet := by tidy,
  ext_join := by simp only [finset.inf_eq_inter, forall_const, iff_self, finset.mem_inter, forall_true_iff],
  ext_compl := by apply finset.mem_compl,
}
end extensionality