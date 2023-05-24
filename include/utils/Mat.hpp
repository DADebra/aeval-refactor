#ifndef __MAT_HPP__
#define __MAT_HPP__

#include <stdlib.h>
#include <string.h>

#include <iostream>
#include <stdexcept>
#include <vector>
#include <functional>
#include <tuple>

namespace mat
{

template <typename Val>
class MatItr
{
  private:
  Val *data;
  unsigned step;

  MatItr(unsigned in_step, Val *in_data) : step(in_step), data(in_data) {}

  public:
  Val &operator*() { return *data; }
  const Val &operator*() const { return *data; }
  Val &operator->() { return *data; }
  const Val &operator->() const { return *data; }

  MatItr<Val> operator++(int)
  { MatItr<Val> cp(*this); data += step; return cp; }
  MatItr<Val> &operator++()
  { data += step; return *this; }
  MatItr<Val> operator--(int)
  { MatItr<Val> cp(*this); data -= step; return cp; }
  MatItr<Val> &operator--()
  { data -= step; return *this; }
};

template <typename T>
class fill_form
{
  std::function<T(void)> func;
  int enumval;
  public:
  fill_form(int ev, std::function<T(void)> _func) : enumval(ev), func(_func) {}

  T operator()() const { return func(); }

  template <typename S>
  bool operator==(const fill_form<S>& oth) const
  { return enumval == oth.enumval; }

  template <typename S>
  friend class fill_form;
};

namespace fill
{
  static int _zeros() { return 0; }
  static int _ones()  { return 1; }
  static const fill_form<int> zeros = fill_form<int>(0, _zeros);
  static const fill_form<int> ones =  fill_form<int>(1, _ones);
  static const fill_form<int> eye =   fill_form<int>(2, _zeros);
  template <typename Val>
  static const fill_form<Val> value(const Val& fillval)
  { return fill_form<Val>(6, [=]() -> Val { return fillval; }); }
  static const fill_form<int> none =  fill_form<int>(7, _zeros);
};

template <typename Val>
class MatBase
{
  protected:
  Val *data; // r0c0, r0c1, r1c0, r1c1, ...
  const unsigned size;
  public:
  const unsigned step;
  const unsigned n_elem;
  const bool owned;

  protected:
  MatBase() : n_elem(0), size(0), data(NULL), step(1), owned(true) {}
  MatBase(unsigned in_size, unsigned in_step, Val* in_data) : size(in_size),
    n_elem(in_size / in_step), data(in_data), step(in_step), owned(false) {}

  MatBase(unsigned in_size, unsigned in_step) : size(in_size),
    n_elem(in_size / in_step), data((Val*)malloc(in_size*sizeof(Val))),
    step(in_step), owned(true)
  {
    for (unsigned i = 0; i < size; i += step)
      new (data + i) Val();
  }

  template <typename T>
  MatBase(const MatBase<T>& oth) : n_elem(oth.n_elem), step(1),
    data((Val*)malloc(oth.n_elem*sizeof(Val))), owned(true), size(oth.n_elem)
  {
    for (unsigned i = 0, j = 0; i < n_elem && j < oth.size; ++i, j += oth.step)
      new (data + i) Val(oth.data[j]);
  }
  MatBase(const MatBase<Val>& oth) : n_elem(oth.n_elem), step(1),
    data((Val*)malloc(oth.n_elem*sizeof(Val))), owned(true), size(oth.n_elem)
  {
    for (unsigned i = 0, j = 0; i < n_elem && j < oth.size; ++i, j += oth.step)
      new (data + i) Val(oth.data[j]);
  }

  MatBase(MatBase<Val>&& oth) : n_elem(oth.n_elem), step(oth.step),
    data(oth.data), owned(oth.owned), size(oth.size)
  { oth.data = NULL; (bool&)oth.owned = false; }

  MatBase<Val>& operator=(const MatBase<Val>& oth)
  {
    if (owned)
    { this->~MatBase<Val>(); new (this) MatBase<Val>(oth); return *this; }
    if (n_elem != oth.n_elem)
      throw new std::invalid_argument(
        "Can't assign differently sized Mat's to each other");
    for (unsigned i = 0, j = 0; i < size && j < oth.size; i += step, j += oth.step)
      data[i] = oth.data[j];
    return *this;
  }

  // [from, to]
  void shed_contig(unsigned from, unsigned to)
  {
    for (unsigned i = from; i < to; ++i)
      data[i].~Val();
    memmove(data + from, data + to, size - to);
    (unsigned&)size = size - (to - from + 1);
    (unsigned&)n_elem = size / step;
    data = (Val*)realloc(data, sizeof(Val) * size);
  }

  void insert_contig(unsigned ii,const MatBase<Val>& newdata,unsigned newelems)
  {
    data = (Val*)realloc(data, sizeof(Val) * (size + newelems));
    memmove(data + ii + newelems, data + ii, sizeof(Val) * (size - ii));
    for (unsigned i = ii, j = 0; i < ii + newelems && j < newdata.size;
     ++i, j += newdata.step)
      new (data + i) Val(newdata.data[j]);
    (unsigned&)size = size + newelems;
    (unsigned&)n_elem = size / step;
  }
  void insert_contig(unsigned ii, const Val& v)
  {
    data = (Val*)realloc(data, sizeof(Val) * (size + 1));
    memmove(data + ii + 1, data + ii, sizeof(Val) * (size - ii));
    new (data + ii) Val(v);
    (unsigned&)size = size + 1;
    (unsigned&)n_elem = size / step;
  }

  public:
  ~MatBase()
  {
    if (owned && data)
    {
      for (unsigned i = 0; i < size; i += step)
        data[i].~Val();
      free(data);
    }
    (bool&)owned = false;
    data = NULL;
  }

  MatBase<Val>& operator=(const Val& v)
  {
    for (unsigned i = 0; i < size; i += step)
      data[i] = v;
    return *this;
  }

  template <typename T>
  MatBase<Val>& fill(const fill_form<T>& form)
  {
    if (form == fill::none)
      return *this;
    if (form == fill::eye)
      throw new std::invalid_argument("Cannot use fill::eye with non-Mat");
    for (unsigned i = 0; i < size; i += step)
      data[i] = form();
    return *this;
  }

  Val &operator[](unsigned i) { return data[i * step]; }
  const Val &operator[](unsigned i) const { return data[i * step]; }
  Val &operator()(unsigned i)
  {
    if (i < 0 || i >= n_elem)
      throw new std::out_of_range("Index out of bounds");
    return data[i * step];
  }
  const Val &operator()(unsigned i) const
  {
    if (i < 0 || i >= n_elem)
      throw new std::out_of_range("Index out of bounds");
    return data[i * step];
  }
  Val &at(unsigned i) { return data[i * step]; }
  const Val &at(unsigned i) const { return data[i * step]; }

  MatItr<Val> begin() { return MatItr<Val>(step, data); }
  const MatItr<Val> begin() const { return MatItr<Val>(step, data); }
  MatItr<Val> end() { return MatItr<Val>(step, data + size); }
  const MatItr<Val> end() const { return MatItr<Val>(step, data + size); }

  bool operator==(const MatBase<Val>& oth) const
  {
    if (n_elem != oth.n_elem)
      return false;
    for (unsigned i = 0, j = 0; i < size && j < oth.size; i += step, j += oth.step)
      if (data[i] != oth.data[j]) return false;
    return true;
  }

  bool operator==(const Val& oth) const
  {
    for (unsigned i = 0; i < size; i += step)
      if (data[i] != oth)
        return false;
    return true;
  }

  bool operator!=(const MatBase<Val>& oth) const
  { return !(*this == oth); }

  bool operator!=(const Val& oth) const
  { return !(*this == oth); }

  void set_size(unsigned new_size)
  {
    if (!owned)
      throw new std::runtime_error("Can't resize non-owned MatBase");
    unsigned old_size;
    (unsigned&)size = new_size;
    (unsigned&)n_elem = size / step;
    data = (Val*)realloc(data, sizeof(Val) * new_size);
    for (unsigned i = old_size; i < new_size; ++i)
      new (data + i) Val();
  }

  Val& min() const
  {
    Val* min = data;
    for (unsigned i = 0; i < size; i += step) if (data[i] < *min) min = data + i;
    return *min;
  }

  Val& max() const
  {
    Val* max = data;
    for (unsigned i = 0; i < size; i += step) if (data[i] > *max) max = data + i;
    return *max;
  }

  template <typename T>
  friend class Mat;
  template <typename T>
  friend class MatBase;
  template <typename T>
  friend class Row;
  template <typename T>
  friend class Col;
};

template <typename Val>
class Row;

template <typename Val>
class Col;

template <typename Val>
class Mat : public MatBase<Val>
{
  private:
  Mat(unsigned in_rows, unsigned in_cols, const MatBase<Val>& oth) :
    MatBase<Val>(oth.size, oth.step, oth.data),
    n_rows(in_rows), n_cols(in_cols) {}

  public:
  unsigned n_rows, n_cols;
  Mat() : MatBase<Val>(), n_rows(0), n_cols(0) {}
  Mat(unsigned in_rows, unsigned in_cols) : MatBase<Val>(in_rows * in_cols, 1),
    n_rows(in_rows), n_cols(in_cols) {}
  template <typename T>
  Mat(unsigned in_rows, unsigned in_cols, const fill_form<T>& ff) :
    MatBase<Val>(in_rows * in_cols, 1), n_rows(in_rows), n_cols(in_cols)
  { MatBase<Val>::fill(ff); }

  template <typename T>
  Mat(const Mat<T> &oth) : MatBase<Val>(oth),
    n_rows(oth.n_rows), n_cols(oth.n_cols) {}
  Mat(const Mat<Val> &oth) : MatBase<Val>(oth),
    n_rows(oth.n_rows), n_cols(oth.n_cols) {}
  Mat(Mat<Val> &&oth) : MatBase<Val>(std::move(oth)),
    n_rows(oth.n_rows), n_cols(oth.n_cols) {}

  /*Mat(const Val& oth) : MatBase<Val>(1, 1), n_rows(1), n_cols(1)
  { this->data[0] = oth; }*/

  Mat<Val> &operator=(const Mat<Val> &oth)
  { this->~Mat<Val>(); new (this) Mat<Val>(oth); return *this; }
  Mat<Val> &operator=(Mat<Val> &&oth)
  { this->~Mat<Val>(); new (this) Mat<Val>(std::move(oth)); return *this; }
  Mat<Val>& operator=(const Val& v)
  { MatBase<Val>::operator=(v); return *this; }


  Val &operator()(unsigned in_row, unsigned in_col)
  {
    if (in_row < 0 || in_row >= n_rows)
      throw new std::out_of_range("Row access out of bounds");
    if (in_col < 0 || in_col >= n_cols)
      throw new std::out_of_range("Column access out of bounds");
    return at(in_row, in_col);
  }
  const Val &operator()(unsigned in_row, unsigned in_col) const
  {
    if (in_row < 0 || in_row >= n_rows)
      throw new std::out_of_range("Row access out of bounds");
    if (in_col < 0 || in_col >= n_cols)
      throw new std::out_of_range("Column access out of bounds");
    return at(in_row, in_col);
  }

  Val &at(unsigned in_row, unsigned in_col)
  {
    if (this->step != 1)
      return this->data[(in_row * in_col) * this->step];
    else
      return this->data[(n_cols * in_row) + in_col];
  }
  const Val &at(unsigned in_row, unsigned in_col) const
  {
    if (this->step != 1)
      return this->data[(in_row * in_col) * this->step];
    else
      return this->data[(n_cols * in_row) + in_col];
  }

  void set_size(unsigned new_rows, unsigned new_cols)
  {
    MatBase<Val>::set_size(new_rows * new_cols);
    (unsigned&)n_rows = new_rows;
    (unsigned&)n_cols = new_cols;
  }

  template <typename T>
  Mat<Val>& fill(const fill_form<T> &ff)
  {
    if (ff == fill::eye)
    {
      if (n_rows != n_cols)
        throw new invalid_argument("Cannot use fill::eye with non-square Mat");
      MatBase<Val>::fill(fill::zeros);
      for (unsigned i = 0; i < n_rows; ++i)
        (*this)(i, i) = 1;
    }
    else
      MatBase<Val>::fill(ff);
    return *this;
  }

  Mat<Val>& fill(const Val &fillval)
  { MatBase<Val>::fill(fill::value(fillval)); return *this; }

  Row<Val> row(unsigned in_row);
  const Row<Val> row(unsigned in_row) const;

  Col<Val> col(unsigned in_col);
  const Col<Val> col(unsigned in_col) const;

  Mat<Val> t() const
  {
    Mat<Val> ret(n_cols, n_rows);
    for (unsigned r = 0; r < n_rows; ++r)
      for (unsigned c = 0; c < n_cols; ++c)
        ret(c, r) = (*this)(r, c);
    return std::move(ret);
  }

  void swap_rows(unsigned r1, unsigned r2)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't swap_rows on view");
    if (this->step != 1)
      throw new std::runtime_error("step != 1 and owned should be impossible");
    Val* tmp = (Val*)malloc(sizeof(Val) * n_cols);
    memcpy(tmp, this->data + (r1 * n_cols), sizeof(Val) * n_cols);
    memcpy(this->data + (r1 * n_cols), this->data + (r2 * n_cols),
      sizeof(Val) * n_cols);
    memcpy(this->data + (r2 * n_cols), tmp, sizeof(Val) * n_cols);
    free(tmp);
  }

  void swap_cols(unsigned c1, unsigned c2)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't swap_cols on view");
    Col<Val> tmp(col(c1));
    col(c1) = col(c2);
    col(c2) = tmp;
  }

  void shed_rows(unsigned r1, unsigned r2)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't shed_rows on view");
    if (this->step != 1)
      throw new std::runtime_error("step != 1 and owned should be impossible");
    this->shed_contig(r1 * n_cols, (r2+1) * n_cols);
    (unsigned&)n_rows = n_rows - (r2 - r1 + 1);
  }

  void shed_row(unsigned r1) { return shed_rows(r1, r1); }

  void shed_cols(unsigned c1, unsigned c2)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't shed_cols on view");
    unsigned diff = c2 - c1 + 1;
    /*for (unsigned i = n_cols - c2 - 1; i < n_cols; ++i)
      col(i - diff) = col(i);*/
    for (unsigned i = c2, j = c1; i < n_cols && j < n_cols; ++i, ++j)
      col(j) = col(i);
    (unsigned&)n_cols = n_cols - diff;
    (unsigned&)this->size = n_rows * n_cols;
    (unsigned&)this->n_elem = this->size / this->step;
    this->data = (Val*)realloc(this->data, sizeof(Val) * this->size);
  }
  void shed_col(unsigned c1) { return shed_cols(c1, c1); }

  void insert_rows(unsigned ri, const Mat<Val>& m)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't insert_rows on view");
    if (this->step != 1)
      throw new std::runtime_error("step != 1 and owned should be impossible");
    if (n_cols == 0)
      (unsigned&)n_cols = m.n_cols;
    if (n_cols != m.n_cols)
      throw new std::invalid_argument("Can't insert_rows with differing n_cols");
    this->insert_contig(ri * n_cols, m, m.n_elem);
    (unsigned&)n_rows = n_rows + m.n_rows;
  }
  void insert_rows(unsigned ri, const Val& v)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't insert_rows on view");
    if (this->step != 1)
      throw new std::runtime_error("step != 1 and owned should be impossible");
    if (n_cols == 0)
      (unsigned&)n_cols = 1;
    if (n_cols != 1)
      throw new std::invalid_argument(
        "Can't insert_rows a value to a Mat with n_cols > 1");
    this->insert_contig(ri * n_cols, v);
    (unsigned&)n_rows = n_rows + 1;
  }

  void insert_cols(unsigned ci, const Mat<Val>& m)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't insert_rows on view");
    if (n_rows == 0)
      (unsigned&)n_rows = m.n_rows;
    if (n_rows != m.n_rows)
      throw new std::invalid_argument("Can't insert_cols with differing n_rows");
    Mat<Val> newmat(n_rows, n_cols + m.n_cols);
    for (unsigned i = 0; i < ci; ++i)
      newmat.col(i) = col(i);
    for (unsigned i = ci; i < ci + m.n_cols; ++i)
      newmat.col(i) = m.col(i - ci);
    for (unsigned i = ci + m.n_cols; i < newmat.n_cols; ++i)
      newmat.col(i) = col(i - m.n_cols);
    this->~Mat<Val>(); new (this) Mat<Val>(std::move(newmat));
  }
  void insert_cols(unsigned ci, const Val& v)
  {
    if (!this->owned)
      throw new std::invalid_argument("Can't insert_rows on view");
    if (n_rows == 0)
      (unsigned&)n_rows = 1;
    if (n_rows != 1)
      throw new std::invalid_argument(
        "Can't insert_cols a value to a Mat with n_rows > 1");
    Mat<Val> newmat(n_rows, n_cols + 1);
    for (unsigned i = 0; i < ci; ++i)
      newmat.col(i) = col(i);
    newmat.col(ci)(0) = v;
    for (unsigned i = ci + 1; i < newmat.n_cols; ++i)
      newmat.col(i) = col(i - 1);
    this->~Mat<Val>(); new (this) Mat<Val>(std::move(newmat));
  }

  friend Row<Val>;
  friend Col<Val>;
  template <typename T>
  friend class conv_to;
};

template <typename Val>
class Row : public MatBase<Val>
{
  public:
  const unsigned n_cols;

  private:
  Row(const Mat<Val> &base, unsigned in_row) : n_cols(base.n_cols),
    MatBase<Val>(base.n_cols, base.step, base.data + (in_row * base.n_cols)) {}
  Row(unsigned in_cols, Val* data) : MatBase<Val>(in_cols, 1, data),
    n_cols(in_cols) {}

  public:
  Row() : MatBase<Val>(), n_cols(0) {}
  explicit Row(unsigned in_cols) : MatBase<Val>(in_cols, 1), n_cols(in_cols) {}
  template <typename T>
  Row(unsigned in_cols, const fill_form<T> &ff) : MatBase<Val>(in_cols, 1),
    n_cols(in_cols)
  { MatBase<Val>::fill(ff); }

  template <typename T>
  Row(const Row<T> &oth) : MatBase<Val>(oth), n_cols(oth.n_cols) {}
  Row(const Row<Val> &oth) : MatBase<Val>(oth), n_cols(oth.n_cols) {}
  Row(Row<Val> &&oth) : MatBase<Val>(std::move(oth)), n_cols(oth.n_cols) {}

  template <typename T>
  Row(const Mat<T> &oth) : MatBase<Val>(oth), n_cols(oth.n_cols)
  {
    if (oth.n_rows != 1)
      throw new std::invalid_argument(
        "Can't construct Row from Mat with > 1 row");
  }
  Row(Mat<Val> &&oth) : MatBase<Val>(std::move(oth)), n_cols(oth.n_cols)
  {
    if (oth.n_rows != 1)
      throw new std::invalid_argument(
        "Can't construct Row from Mat with > 1 row");
  }

  Row(const Col<Val> &oth) : MatBase<Val>(oth), n_cols(oth.n_elem) {}
  Row(Col<Val> &&oth) : MatBase<Val>(std::move(oth)), n_cols(oth.n_elem) {}

  Row<Val> &operator=(const MatBase<Val> &oth)
  { MatBase<Val>::operator=(oth); return *this; }
  Row<Val> &operator=(const Row<Val> &oth)
  { MatBase<Val>::operator=(oth); return *this; }
  Row<Val>& operator=(const Val& v)
  { MatBase<Val>::operator=(v); return *this; }

  void set_size(unsigned new_cols)
  {
    MatBase<Val>::set_size(new_cols);
    (unsigned&)n_cols = new_cols;
  }

  Row<Val>& fill(const Val &fillval)
  { MatBase<Val>::fill(fill::value(fillval)); return *this; }

  operator Mat<Val>() {return Mat<Val>(Mat<Val>(1, n_cols, *this));}
  operator const Mat<Val>() const { return Mat<Val>(1, n_cols, *this); }

  Col<Val> t() { return Col<Val>(Col<Val>(n_cols, this->data)); }
  const Col<Val> t() const { return Col<Val>(n_cols, this->data); }

  void shed_cols(unsigned r1, unsigned r2)
  { (unsigned&)n_cols = n_cols - r2 - r1 + 1; this->shed_contig(r1, r2); }
  void shed_row(unsigned r1) { return shed_cols(r1, r1); }

  void insert_cols(unsigned ri, const Mat<Val>& m)
  {
    if (m.n_rows != 1)
      throw new std::invalid_argument("Can't insert_cols with differing n_rows");
    (unsigned&)n_cols = n_cols + m.n_cols;
    this->insert_contig(ri, m, m.n_cols);
  }
  void insert_cols(unsigned ri, const Val& v)
  {
    (unsigned&)n_cols = n_cols + 1;
    this->insert_contig(ri, v);
  }

  friend Mat<Val>;
  friend Col<Val>;
  template <typename T>
  friend class conv_to;
};

template <typename Val>
class Col : public MatBase<Val>
{
  public:
  const unsigned n_rows;

  private:
  Col(const Mat<Val> &base, unsigned in_col) : n_rows(base.n_rows),
    MatBase<Val>(base.size, base.step == 1 ? base.n_cols : base.step,
    base.data + in_col) {}
  Col(unsigned in_rows, Val* data) : MatBase<Val>(in_rows, 1, data),
    n_rows(in_rows) {}

  public:
  Col() : MatBase<Val>(), n_rows(0) {}
  explicit Col(unsigned in_rows) : MatBase<Val>(in_rows, 1), n_rows(in_rows) {}
  template <typename T>
  Col(unsigned in_rows, const fill_form<T> &ff) : MatBase<Val>(in_rows, 1),
    n_rows(in_rows)
  { MatBase<Val>::fill(ff); }

  template <typename T>
  Col(const Col<T> &oth) : MatBase<Val>(oth), n_rows(oth.n_rows) {}
  Col(const Col<Val> &oth) : MatBase<Val>(oth), n_rows(oth.n_rows) {}
  Col(Col<Val> &&oth) : MatBase<Val>(std::move(oth)), n_rows(oth.n_rows) {}

  template <typename T>
  Col(const Mat<T> &oth) : MatBase<Val>(oth), n_rows(oth.n_rows)
  {
    if (oth.n_cols != 1)
      throw new std::invalid_argument(
        "Can't construct Col from Mat with > 1 column");
  }
  Col(Mat<Val> &&oth) : MatBase<Val>(std::move(oth)), n_rows(oth.n_rows)
  {
    if (oth.n_cols != 1)
      throw new std::invalid_argument(
        "Can't construct Col from Mat with > 1 column");
  }

  Col(const Row<Val> &oth) : MatBase<Val>(oth), n_rows(oth.n_elem) {}
  Col(Row<Val> &&oth) : MatBase<Val>(std::move(oth)), n_rows(oth.n_elem) {}

  Col<Val> &operator=(const MatBase<Val> &oth)
  { MatBase<Val>::operator=(oth); return *this; }
  Col<Val> &operator=(const Col<Val> &oth)
  { MatBase<Val>::operator=(oth); return *this; }
  Col<Val>& operator=(const Val& v)
  { MatBase<Val>::operator=(v); return *this; }

  void set_size(unsigned new_rows)
  {
    MatBase<Val>::set_size(new_rows);
    (unsigned&)n_rows = new_rows;
  }

  Col<Val>& fill(const Val &fillval)
  { MatBase<Val>::fill(fill::value(fillval)); return *this; }

  operator Mat<Val>() { return Mat<Val>(Mat<Val>(n_rows, 1, *this)); }
  operator const Mat<Val>() const { return Mat<Val>(n_rows, 1, *this); }

  Row<Val> t() { return Row<Val>(Row<Val>(n_rows, this->data)); }
  const Row<Val> t() const { return Row<Val>(n_rows, this->data); }

  void shed_rows(unsigned c1, unsigned c2)
  { (unsigned&)n_rows = n_rows - c2 - c1 + 1; this->shed_contig(c1, c2); }
  void shed_col(unsigned c1) { return shed_rows(c1, c1); }

  void insert_rows(unsigned ci, const Mat<Val>& m)
  {
    if (m.n_cols != 1)
      throw new std::invalid_argument("Can't insert_rows with differing n_cols");
    (unsigned&)n_rows = n_rows + m.n_rows;
    this->insert_contig(ci, m, m.n_rows);
  }
  void insert_rows(unsigned ci, const Val& v)
  {
    (unsigned&)n_rows = n_rows + 1;
    this->insert_contig(ci, v);
  }

  friend Mat<Val>;
  friend Row<Val>;
};

template <typename Val>
Row<Val> Mat<Val>::row(unsigned in_row) { return Row<Val>(*this, in_row); }
template <typename Val>
const Row<Val> Mat<Val>::row(unsigned in_row) const
{ return Row<Val>(*this, in_row); }

template <typename Val>
Col<Val> Mat<Val>::col(unsigned in_col) { return Col<Val>(*this, in_col); }
template <typename Val>
const Col<Val> Mat<Val>::col(unsigned in_col) const
{ return Col<Val>(*this, in_col); }




template <typename Val>
Mat<Val> trans(const Mat<Val>& A) { return A.t(); }
template <typename Val>
Row<Val> trans(const Col<Val>& A) { return A.t(); }
template <typename Val>
Col<Val> trans(const Row<Val>& A) { return A.t(); }

template <typename Val>
bool approx_equal(const Mat<Val>& A, const Mat<Val>& B,
  const char *method, const Val& tol)
{
  if (A.n_rows != B.n_rows || A.n_cols != B.n_cols)
    return false;
  if (!strcmp(method, "both"))
    throw new std::invalid_argument(
      "abs_tol and rel_tol must be given when method is \"both\"");
  if (strcmp(method, "reldiff") && strcmp(method, "absdiff"))
    throw new std::invalid_argument("invalid method");
  bool reldiff = !strcmp(method, "reldiff");
  for (unsigned i = 0; i < A.n_elem; ++i)
  {
    Val diff = abs(A[i] - B[i]);
    if (reldiff)
      diff = diff / max(abs(A[i]), abs(B[i]));
    if (diff > tol)
      return false;
  }
  return true;
}

template <typename Val>
bool approx_equal(const Mat<Val>& A, const Mat<Val>& B,
  const char *method, const Val& abs_tol, const Val& rel_tol)
{
  if (A.n_rows != B.n_rows || A.n_cols != B.n_cols)
    return false;
  if (strcmp(method, "both"))
    throw new std::invalid_argument(
      "method must be \"both\" when abs_tol and rel_tol are given");
  for (unsigned i = 0; i < A.n_elem; ++i)
  {
    Val absdiff = abs(A[i] - B[i]);
    Val reldiff = absdiff / max(abs(A[i]), abs(B[i]));
    if (absdiff > abs_tol && reldiff > rel_tol)
      return false;
  }
  return true;
}

template <typename T>
class conv_to
{
  public:
  template <typename Val>
  static T from(const Mat<Val>& m) { return T(T(m)); }
  template <typename Val>
  static T from(const Col<Val>& m) { return T(T(m)); }
  template <typename Val>
  static T from(const Row<Val>& m) { return T(T(m)); }
  template <typename Val>
  static Col<Val> from(const Row<Val>& m)
  { return Col<Val>(Col<Val>(m.n_cols, m.data)); }

  template <typename Val>
  static T from(const std::vector<Val>& v) {
    T ret(v.size());
    for (unsigned i = 0; i < v.size(); ++i) ret[i] = v[i];
    return std::move(ret);
  }
};

// Same as 'solve' but with A and B already combined
template <typename Val>
bool solvecomb(Mat<Val>& X, Mat<Val> input)
{
  // Originally from rnd/DataLearner.hpp
  unsigned int cur_row = 0;
  unsigned int cur_col = 0;
  Col<unsigned int> rowToPivot = Col<unsigned int>(input.n_rows);
  const unsigned int UNDEFINED_PIVOT = 100;

  rowToPivot.fill(UNDEFINED_PIVOT);

  //printmsg(DEBUG, "Before row\n", input);

  //row echleon form
  while (cur_col < input.n_cols && cur_row < input.n_rows) {

    if (input(cur_row, cur_col) == 0) {
      unsigned int next_nonzero;
      for (next_nonzero = cur_row; next_nonzero < input.n_rows; next_nonzero++) {
        if (input(next_nonzero, cur_col) != 0) {
          break;
        }
      }
      if (next_nonzero == input.n_rows) {
        cur_col++;
        continue;
      } else {
        input.swap_rows(cur_row, next_nonzero);
      }
    }

    if (input(cur_row, cur_col) != 1) {
      Val inverse = 1/input(cur_row, cur_col);
      for (unsigned int k = cur_col; k < input.n_cols; k++) {
        input(cur_row, k) = input(cur_row,k)*inverse;
      }
    }

    for (unsigned int j = cur_row+1; j < input.n_rows; j++) {
      Val f = input(j, cur_col)/input(cur_row, cur_col);
      for (unsigned int k = 0; k < input.n_cols; k++) {
        input(j,k) = input(j,k) - input(cur_row, k)*f;
      }
      input(j,cur_col) = 0;
    }

    rowToPivot(cur_row) = cur_col;

    cur_col++;
    cur_row++;
  }

  rowToPivot(input.n_rows-1) = input.n_cols-1;

  //reduced row echloen form
  if (cur_row != input.n_rows) {
    //we have found a zero row before we reached last row
    cur_row = cur_row-1;
  } else {
    cur_row = input.n_rows-1;
  }

  cur_col = rowToPivot(cur_row);

  while (cur_row < input.n_rows) {

    cur_col = rowToPivot(cur_row);

    if (cur_col == UNDEFINED_PIVOT || input(cur_row,cur_col) == 0) {
      cur_row--;
      continue;
    }

    for (unsigned int j = cur_row-1; j < input.n_rows; j--) {
      Val f = input(j,cur_col)/input(cur_row,cur_col);
      for (unsigned int k = 0; k < input.n_cols; k++) {
        input(j,k) = input(j,k) - input(cur_row,k)*f;
      }
    }
    cur_row--;
  }

  //      printmsg(INFO, "after row reduced\n", input);

  std::vector<unsigned int> independentVars;

  for (unsigned col = 0; col < input.n_cols; col++) {
    if (col < input.n_rows && input(col, col) == 0) {
      independentVars.push_back(col);
    }
  }

  if (independentVars.size() == 0)
    return false;

  X = Mat<Val>(input.n_cols, independentVars.size());
  X.fill(0);
  unsigned int x_col = 0;

  for (auto indVar : independentVars) {
    for (unsigned int row = 0; row < input.n_rows; row++) {
      if (rowToPivot[row] == UNDEFINED_PIVOT) {
        continue;
      }
      //TODO: replace -2 with lcm of column
      //printmsg(DEBUG, input(row,indVar), row, indVar);
      X(rowToPivot(row), x_col) = -1*input(row, indVar);
    }
    X(indVar, x_col)=1;
    x_col++;
  }

  /*bool firstzeros = true;
  for (unsigned r = 0; r < X.n_rows - 1; ++r)
    if (X(r, X.n_cols-1) != 0)
    { firstzeros = false; break; }

  if (firstzeros && X(X.n_rows-1, X.n_cols-1) != 0)
  {
    X = Mat<Val>();
    return false;
  }*/

  return true;
}

template <typename Val>
Mat<Val> solvecomb(const Mat<Val>& A)
{
  Mat<Val> retmat;
  bool retb = solvecomb<Val>(retmat, A);
  if (!retb)
    throw new std::runtime_error("No solution to A*X = B");
  return std::move(retmat);
}

template <typename Val>
bool solve(Mat<Val>& X, const Mat<Val>& A, const Mat<Val>& B)
{
  Mat<Val> input(A);
  if (B.n_rows == 1 && B.n_cols > 1)
    input.insert_cols(input.n_cols, B.t());
  else
    input.insert_cols(input.n_cols, B);
  return solvecomb<Val>(X, std::move(input));
}

template <typename Val>
Mat<Val> solve(const Mat<Val>& A, const Mat<Val>& B)
{
  Mat<Val> retmat;
  bool retb = solve<Val>(retmat, A, B);
  if (!retb)
    throw new std::runtime_error("No solution to A*X = B");
  return std::move(retmat);
}

template <typename Val>
Val& min(const Row<Val> &m) { return m.min(); }
template <typename Val>
Val& min(const Col<Val> &m) { return m.min(); }
template <typename Val>
Mat<Val> min(const Mat<Val>& m, unsigned dim)
{
  Mat<Val> ret;
  if (dim == 0)
  {
    for (int i = 0; i < m.n_rows; ++i)
      ret.insert_cols(ret.n_cols, m.row(i).min());
  }
  else if (dim == 1)
  {
    for (int i = 0; i < m.n_cols; ++i)
      ret.insert_rows(ret.n_rows, m.col(i).min());
  }
  else
    throw new std::invalid_argument("dim must be 0 or 1");
  return std::move(ret);
}

template <typename Val>
Val& max(const Row<Val> &m) { return m.min(); }
template <typename Val>
Val& max(const Col<Val> &m) { return m.min(); }
template <typename Val>
Mat<Val> max(const Mat<Val>& m, unsigned dim)
{
  Mat<Val> ret;
  if (dim == 0)
  {
    for (int i = 0; i < m.n_rows; ++i)
      ret.insert_cols(ret.n_cols, m.row(i).max());
  }
  else if (dim == 1)
  {
    for (int i = 0; i < m.n_cols; ++i)
      ret.insert_rows(ret.n_rows, m.col(i).max());
  }
  else
    throw new std::invalid_argument("dim must be 0 or 1");
  return std::move(ret);
}

typedef Mat<double> mat;
typedef Mat<double> dmat;
typedef Mat<float> fmat;
typedef Mat<unsigned> umat;
typedef Mat<int> imat;

typedef Col<double> colvec;
typedef Col<double> dcolvec;
typedef Col<float> fcolvec;
typedef Col<unsigned> ucolvec;
typedef Col<int> icolvec;

typedef Row<double> rowvec;
typedef Row<double> drowvec;
typedef Row<float> frowvec;
typedef Row<unsigned> urowvec;
typedef Row<int> irowvec;

typedef colvec vec;
typedef dcolvec dvec;
typedef fcolvec fvec;
typedef ucolvec uvec;
typedef icolvec icec;

}

namespace std
{
  template <typename Val>
  std::ostream& operator<<(std::ostream& o, const mat::Mat<Val>& m)
  {
    for (int r = 0; r < m.n_rows; ++r)
    {
      if (r != 0)
        o << '\n';
      else
        o << "Mat(";
      for (int c = 0; c < m.n_cols; ++c)
        o << '	' << m(r,c);
    }
    o << ")";
    o.flush();
    return o;
  }
  template <typename Val>
  std::ostream& operator<<(std::ostream& o, const mat::Col<Val>& m)
  {
    o << "Col(";
    for (int r = 0; r < m.n_rows; ++r)
    {
      if (r != 0)
        o << ',';
      o << m(r);
    }
    o << ")";
    o.flush();
    return o;
  }
  template <typename Val>
  std::ostream& operator<<(std::ostream& o, const mat::Row<Val>& m)
  {
    o << "Row(";
    for (int c = 0; c < m.n_cols; ++c)
    {
      if (c != 0)
        o << ',';
      o << m(c);
    }
    o << ")";
    o.flush();
    return o;
  }
}

#endif
