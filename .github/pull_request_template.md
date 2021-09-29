_Description of your PR_

## Checklist for the reviewer
### General
- [ ] All functions have unit tests

### Functions constructing generators of maximal subgroups
- [ ] The code which computes and then stores the sizes is correct. To do this one confers to the tables referenced by the code. Tests for the group size should use `RECOG.TestGroup` from the recog package.
- [ ] The test suite checks whether all constructed generators are sensible. That is it tests the generators'
  - [ ] determinants (and if applicable also the spinor norms are correct), and
  - [ ] compatibility with the correct form.

### Functions assembling the list of all maximal subgroups of a certain group
- [ ] The code agrees with the tables in section 8.2 of the book "The Maximal Subgroups of the Low-dimensional Finite Classical Groups".

The reviewer doesn't need to compare our results to magma's results. That's the job of the person implementing the code.
